/*
 * FreeRTOS-Plus-TCP NetworkInterface Driver for Designware QOS MAC
 *
 * Author   : Silesh C V <silesh@alifsemi.com>
 *
 * Copyright (C) 2022 ALIF SEMICONDUCTOR
 *
 *  Redistribution and use in source and binary forms, with or without
 *  modification, are permitted provided that the following conditions are met:
 *  - Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 *  - Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *  - Neither the name of ALIF SEMICONDUCTOR nor the names of its contributors
 *    may be used to endorse or promote products derived from this software
 *    without specific prior written permission.
 *
 *  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 *  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 *  IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 *  ARE DISCLAIMED. IN NO EVENT SHALL COPYRIGHT HOLDERS AND CONTRIBUTORS BE
 *  LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
 *  CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
 *  SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 *  INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
 *  CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 *  ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 *  POSSIBILITY OF SUCH DAMAGE.
 */

/**
 * @file NetworkInterface.c
 * @brief Implements the Ethernet MAC NetworkInterface Driver.
 */

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_Sockets.h"
#include "NetworkInterface.h"
#include "NetworkBufferManagement.h"

#include "phyHandling.h"
#include "FreeRTOS_Routing.h"

/* Driver includes */
#include "mac_hw.h"
#include "pinconf.h"
#include "sys_ctrl_eth.h"
#include <string.h>

#define HANDLER_TASK_STACK_SIZE         2048ul /**< 512 overflowed in snprintf/vfprintf (STKOF). */

#ifndef niDESCRIPTOR_WAIT_TIME_MS
	#define niDESCRIPTOR_WAIT_TIME_MS   250ul /**< Maximum time to wait for a free Tx Descriptor. */
#endif

/* M55 DCCMVAC/DCIMVAC are 32-byte ops. CMSIS writes the unaligned pointer
 * as-is; on this core that UsageFaults on the first TX (buffer is
 * pucEthernetBuffer at +ipBUFFER_PADDING, typically +10). */
#define ETH_DCACHE_LINE    32u

static void prvDCacheClean( void * pvAddr, size_t xSize )
{
    uintptr_t ulStart;
    uintptr_t ulEnd;

    if( ( pvAddr == NULL ) || ( xSize == 0u ) )
    {
        return;
    }

    ulStart = ( uintptr_t ) pvAddr & ~( uintptr_t )( ETH_DCACHE_LINE - 1u );
    ulEnd   = ( ( uintptr_t ) pvAddr + xSize + ( ETH_DCACHE_LINE - 1u ) )
              & ~( uintptr_t )( ETH_DCACHE_LINE - 1u );
    SCB_CleanDCache_by_Addr( ( void * ) ulStart, ( int32_t ) ( ulEnd - ulStart ) );
}

static void prvDCacheInvalidate( void * pvAddr, size_t xSize )
{
    uintptr_t ulStart;
    uintptr_t ulEnd;

    if( ( pvAddr == NULL ) || ( xSize == 0u ) )
    {
        return;
    }

    ulStart = ( uintptr_t ) pvAddr & ~( uintptr_t )( ETH_DCACHE_LINE - 1u );
    ulEnd   = ( ( uintptr_t ) pvAddr + xSize + ( ETH_DCACHE_LINE - 1u ) )
              & ~( uintptr_t )( ETH_DCACHE_LINE - 1u );
    SCB_InvalidateDCache_by_Addr( ( void * ) ulStart, ( int32_t ) ( ulEnd - ulStart ) );
}

/* private functions */

/* Initialise the hardware */
static BaseType_t prvEqosHwInit( DwEqosDev * pxEthDev );

/* Set up descriptors */
static void prvInitDescriptors( DwEqosDev * pxEthDev );
static void prvInitTxDescs( DwEqosDev * pxEthDev );
static void prvInitRxDescs( DwEqosDev * pxEthDev );

/* Task to process received Frames */
static void prvEqosHandlerTask( void * pvParamaters );

/* set a given mac address in the hardware */
static void prvSetMacAddr( DwEqosDev * pxEthDev, const uint8_t * ucAddress );

/* MAC instance used */
static DwEqosDev EQOS0 = {
    .pxRegs = (volatile DW_EQOS_REGS *) ETH_BASE,
    .xIrq = ETH_SBD_IRQ_IRQn,
#if ( ipconfigETHERNET_AN_ENABLE != 0 )
    .Config = {
        .ucAutoNegCtrl = AN_ENABLE,
    },
#else
	.Config = {
	        .ucAutoNegCtrl = AN_DISABLE,
	#if ( ipconfigETHERNET_USE_100MB != 0 )
			.ucSpeed  = ETH_SPEED_100M,
    #else
			.ucSpeed  = ETH_SPEED_10M,
    #endif

    #if ( ipconfigETHERNET_USE_FULL_DUPLEX != 0 )
			.ucDuplex = ETH_DUPLEX_FULL,
	#else
			.ucDuplex = ETH_DUPLEX_HALF,
    #endif
	},
#endif
};

/** @brief Flag receive buffer unavailable condition. */
static volatile uint32_t ulRbuFlag;

/** @brief Our MAC address, defined in the application. */
extern uint8_t ucMACAddress[ 6 ];

/*
 * Events signalled from the ISR. Note that Receive buffer unavailable
 * condition is currently indicated as an Rx event.
 */
#define EQOS_RX_EVENT     1UL /**< Signal a Rx event to the task. */
#define EQOS_TX_EVENT     2UL /**< Signal a Tx complete event to the task. */
#define EQOS_ALL_EVENT    ( EQOS_RX_EVENT | EQOS_TX_EVENT )

/** @brief Pending ISR Events to be processed */
static volatile uint32_t  ulISREvents;

/** @brief FreeRTOS phyhandling PHY object. */
static EthernetPhy_t xPhyObject;

/** @brief FreeRTOS PHY properties object. */
const PhyProperties_t xPHYProperties =
{
#if ( ipconfigETHERNET_AN_ENABLE != 0 )
    .ucSpeed      = PHY_SPEED_AUTO,
    .ucDuplex     = PHY_DUPLEX_AUTO,
#else
    #if ( ipconfigETHERNET_USE_100MB != 0 )
        .ucSpeed  = PHY_SPEED_100,
    #else
        .ucSpeed  = PHY_SPEED_10,
    #endif

    #if ( ipconfigETHERNET_USE_FULL_DUPLEX != 0 )
        .ucDuplex = PHY_DUPLEX_FULL,
    #else
        .ucDuplex = PHY_DUPLEX_HALF,
    #endif
#endif /* if ( ipconfigETHERNET_AN_ENABLE != 0 ) */

#if ( ipconfigETHERNET_AN_ENABLE != 0 ) && ( ipconfigETHERNET_AUTO_CROSS_ENABLE != 0 )
    .ucMDI_X      = PHY_MDIX_AUTO,
#elif ( ipconfigETHERNET_CROSSED_LINK != 0 )
    .ucMDI_X      = PHY_MDIX_CROSSED,
#else
    .ucMDI_X      = PHY_MDIX_DIRECT,
#endif
};

/** @brief Handle for the task that handles Rx Packets. */
static TaskHandle_t xRxHandlerTask = NULL;

/** @brief Counting semaphore for resource handling of Tx descriptors. */
static SemaphoreHandle_t xTXDescriptorSemaphore = NULL;

/** @brief Rx DMA Descriptors */
static DmaDesc RxDmaDescs[ RX_DESC_COUNT ] __attribute__( ( section( "eth_buf" ) ) ) __attribute__( ( aligned( 32 ) ) );

/** @brief Tx DMA Descriptors */
static DmaDesc TxDmaDescs[ TX_DESC_COUNT ] __attribute__( ( section( "eth_buf" ) ) ) __attribute__( ( aligned( 32 ) ) );

/** @brief Rx Buffer Descriptors */
static NetworkBufferDescriptor_t *RxBufferDescs[ RX_DESC_COUNT ];

#if ( ipconfigZERO_COPY_RX_DRIVER == 0 )
/** @brief Static Rx buffers, used only if zero copy rx is disabled. */
static uint32_t RxBuffers[ RX_DESC_COUNT ][ ETH_BUF_SIZE >> 2 ] __attribute__( ( section( "eth_buf" ) ) ) __attribute__( ( aligned( 32 ) ) );
#endif /* ipconfigZERO_COPY_RX_DRIVER */

#if ( ipconfigZERO_COPY_TX_DRIVER == 0 )
/** @brief Static tx buffers, used only if zero copy tx is disabled. */
static uint32_t TxBuffers[ TX_DESC_COUNT ][ ETH_BUF_SIZE >> 2 ] __attribute__( ( section( "eth_buf" ) ) ) __attribute__( ( aligned( 32 ) ) );
#endif /* ipconfigZERO_COPY_TX_DRIVER */

/**
 * @brief Initialize the Tx DMA Descriptors
 *
 * @param[in]: pxEthDev Pointer to the DwEqosDev structure.
 */
static void prvInitTxDescs( DwEqosDev * pxEthDev )
{
    uint32_t ul;

    for ( ul = 0; ul < TX_DESC_COUNT; ul++ )
        pxEthDev->TxDescs[ ul ] = ( DmaDesc ) { 0 };

    pxEthDev->pxRegs->DMA_CH0_TX_BASE_ADDR = ( uint32_t ) LocalToGlobal( pxEthDev->TxDescs );
    pxEthDev->pxRegs->DMA_CHO_TX_RING_LEN = TX_DESC_COUNT - 1;

    prvDCacheClean( pxEthDev->TxDescs, TX_DESC_COUNT * sizeof( DmaDesc ) );
}

/**
 * @brief Initialize the Rx DMA Descriptors
 *
 * @param[in]: pxEthDev Pointer to the DwEqosDev structure.
 */
static void prvInitRxDescs( DwEqosDev * pxEthDev )
{
    uint32_t ul, ulLastRxDesc;
    DmaDesc * pxDesc;

    for (ul = 0; ul < RX_DESC_COUNT; ul++)
    {
        pxDesc = &pxEthDev->RxDescs[ ul ];
        #if ( ipconfigZERO_COPY_RX_DRIVER != 0 )
        {
            NetworkBufferDescriptor_t * pxBuffer;
            pxBuffer = pxGetNetworkBufferWithDescriptor( ETH_BUF_SIZE, 100ul );

            configASSERT( pxBuffer != NULL );

            if( pxBuffer != NULL )
            {
                pxDesc->ulDes0 = ( uint32_t ) ( LocalToGlobal( pxBuffer->pucEthernetBuffer ) );
                /* save the NetworkBufferDescriptor_t pointer for this DMA descriptor */
                pxEthDev->pxRxBufferDescs[ ul ] = pxBuffer;
            }
        }
        #else /* if ( ipconfigZERO_COPY_RX_DRIVER != 0 ) */
        {
            pxDesc->ulDes0 = ( uint32_t ) ( LocalToGlobal( &RxBuffers[ ul ][ 0 ] ) );
        }
        #endif
        pxDesc->ulDes3 = RDES3_OWN | RDES3_INT_ON_COMPLETION_EN | RDES3_BUFFER1_VALID_ADDR;
    }


    pxEthDev->pxRegs->DMA_CH0_RX_BASE_ADDR = ( uint32_t ) LocalToGlobal( pxEthDev->RxDescs );
    pxEthDev->pxRegs->DMA_CH0_RX_RING_LEN = RX_DESC_COUNT - 1;

    ulLastRxDesc = ( uint32_t ) LocalToGlobal( &( pxEthDev->RxDescs[ RX_DESC_COUNT - 1 ] ) );

    pxEthDev->pxRegs->DMA_CH0_RX_END_ADDR = ulLastRxDesc;

    prvDCacheClean( pxEthDev->RxDescs, RX_DESC_COUNT * sizeof( DmaDesc ) );
}

/**
 * @brief Set the chosen MAC address in the controller's register.
 *
 * @param[in] pxEthDev: Pointer to the DwEqosDev structure.
 * @param[in] ucAddress: MAC Address
 */
static void prvSetMacAddr( DwEqosDev * pxEthDev, const uint8_t * ucAddress )
{
    uint32_t ulHi, ulLo;

    if ( !ucAddress )
        return;

    ulHi = ( ucAddress[ 5 ] <<  8) |  ucAddress[ 4 ] | EQOS_MAC_ADDR_HIGH_AE;
    ulLo = ( ucAddress[ 3 ] << 24) | (ucAddress[ 2 ] << 16) |
            ( ucAddress[ 1 ] <<  8) |  ucAddress[ 0 ];

    pxEthDev->pxRegs->MAC_ADDR_LOW_0 = ulLo;
    pxEthDev->pxRegs->MAC_ADDR_HIGH_0 = ulHi;
}

/**
 * @brief MAC Hardware instance specific utility function for Eqos_PhyRead().
 *
 * @param[in] xAddress: The PHY address.
 * @param[in] xRegister: Register address.
 * @param[out] pulData: Address to store the read value.
 * @param[in] pxEthDev: Pointer to the DwEqosDev structure.
 */
BaseType_t EqosHwPhyRead( BaseType_t xAddress, BaseType_t xRegister, uint32_t * pulData,
        DwEqosDev * pxEthDev )
{
    uint32_t ulVal, ulTimeout = 5;

    ulVal = ( xAddress << EQOS_MAC_MDIO_ADDR_PA_SHIFT ) |
            ( xRegister << EQOS_MAC_MDIO_ADDR_RDA_SHIFT ) |
            ( EQOS_MAC_MDIO_ADDR_GOC_READ << EQOS_MAC_MDIO_ADDR_GOC_SHIFT ) |
            ( EQOS_MAC_MDIO_ADDR_CR_150_250 << EQOS_MAC_MDIO_ADDR_CR_SHIFT )|
            EQOS_MAC_MDIO_ADDR_GB;

    pxEthDev->pxRegs->MAC_MDIO_ADDR = ulVal;

    do
    {
        if ( ! ( pxEthDev->pxRegs->MAC_MDIO_ADDR & EQOS_MAC_MDIO_ADDR_GB ) )
        {
            *pulData = pxEthDev->pxRegs->MAC_MDIO_DATA;
            break;
        }

        vTaskDelay( pdMS_TO_TICKS( 1 ) );
        ulTimeout--;
    } while ( ulTimeout );

    if ( !ulTimeout )
        return pdFAIL;

    return pdPASS;
}

/**
 * @brief MAC Hardware instance specific utility function for Eqos_PhyWrite()
 *
 * @param[in] xAddress: The PHY address.
 * @param[in] xRegister: Register address.
 * @param[in] ulData: Value to be written.
 * @param[in] pxEthDev: Pointer to the DwEqosDev structure.
 */
BaseType_t EqosHwPhyWrite( BaseType_t xAddress, BaseType_t xRegister, uint32_t ulData,
    DwEqosDev * pxEthDev)
{
    uint32_t ulVal, ulTimeout = 5;

    ulVal = ( xAddress << EQOS_MAC_MDIO_ADDR_PA_SHIFT ) |
                ( xRegister << EQOS_MAC_MDIO_ADDR_RDA_SHIFT ) |
                ( EQOS_MAC_MDIO_ADDR_GOC_WRITE << EQOS_MAC_MDIO_ADDR_GOC_SHIFT ) |
                ( EQOS_MAC_MDIO_ADDR_CR_150_250 << EQOS_MAC_MDIO_ADDR_CR_SHIFT ) |
                EQOS_MAC_MDIO_ADDR_GB;

    pxEthDev->pxRegs->MAC_MDIO_DATA = ulData;
    pxEthDev->pxRegs->MAC_MDIO_ADDR = ulVal;

    do {
        if( !( pxEthDev->pxRegs->MAC_MDIO_ADDR & EQOS_MAC_MDIO_ADDR_GB ) )
            break;
        vTaskDelay( pdMS_TO_TICKS( 1 ) );
        ulTimeout--;
    } while( ulTimeout );

    if ( !ulTimeout )
        return pdFAIL;

    return pdPASS;
}

/**
 * @brief Read a PHY register over MDIO.
 *
 * @param[in] xAddress: The PHY address.
 * @param[in] xRegister: Register address.
 * @param[out] pulValue: Address to store the read value.
 */
BaseType_t Eqos_PhyRead( BaseType_t xAddress, BaseType_t xRegister, uint32_t * pulValue )
{
    return EqosHwPhyRead( xAddress, xRegister, pulValue, &EQOS0 );
}

/**
 * @brief Write into a PHY register over MDIO.
 *
 * @param[in] xAddress: The PHY address.
 * @param[in] xRegister: Register address.
 * @param[in] ulValue: Value to be written.
 */
BaseType_t Eqos_PhyWrite( BaseType_t xAddress, BaseType_t xRegister, uint32_t ulValue )
{
    return EqosHwPhyWrite( xAddress, xRegister, ulValue, &EQOS0 );
}

/**
 * @brief MAC interrupt handler.
 *
 * Handles Tx complete, Rx and recieve buffer unavailable conditions and notifies
 * the handler task.
 *
 * @param pvArg: Unused.
 */
void ETH_SBD_IRQHandler( void )
{
    BaseType_t xHigherPriorityTaskWoken = pdFALSE;
    uint32_t ulStat, ulCh0Stat;

    DwEqosDev * pxEthDev = &EQOS0;

    ulStat = pxEthDev->pxRegs->DMA_STATUS;

    if( ulStat & DMA_STATUS_CHAN0 )
    {
        ulCh0Stat = pxEthDev->pxRegs->DMA_CH0_STATUS;

        pxEthDev->pxRegs->DMA_CH0_STATUS = ulCh0Stat & ( DMA_CHAN_STATUS_NIS | DMA_CHAN_STATUS_RI | DMA_CHAN_STATUS_TI );

        if( ulCh0Stat  & DMA_CHAN_STATUS_RBU )
        {
            /* Do not stop RE/SR. Pack used to gate RX here and then
             * missed the restart if the next IRQ was delayed. */
            pxEthDev->pxRegs->DMA_CH0_STATUS = ulCh0Stat & ( DMA_CHAN_STATUS_AIS | DMA_CHAN_STATUS_RBU );
            ulISREvents |= EQOS_RX_EVENT;
            ulRbuFlag = 1;

            if( xRxHandlerTask != NULL )
            {
                vTaskNotifyGiveFromISR( xRxHandlerTask, &xHigherPriorityTaskWoken );
                portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
            }
        }

        if( ulCh0Stat & DMA_CHAN_STATUS_RI )
        {
            ulISREvents |= EQOS_RX_EVENT;

            if( xRxHandlerTask != NULL )
            {
                vTaskNotifyGiveFromISR( xRxHandlerTask, &xHigherPriorityTaskWoken );
                portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
            }
        }

        if( ulCh0Stat & DMA_CHAN_STATUS_TI )
        {
            ulISREvents |= EQOS_TX_EVENT;

            if( xRxHandlerTask != NULL )
            {
                vTaskNotifyGiveFromISR( xRxHandlerTask, &xHigherPriorityTaskWoken );
                portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
            }
        }
    }
}
/**
 * @brief Discover and initialize the PHY.
 *
 * This function registers the Phy read/write function pointers with the FreeRTOS
 * PHY handling code. After this, calls the FreeRTOS generic/common PHY handling
 * APIs to probe for PHYs connected on the MDIO interface of the MAC and for the
 * PHYs that are found configures/initializes them with the given settings.
 */

void prvPhyInit( void )
{
    vPhyInitialise( &xPhyObject, Eqos_PhyRead, Eqos_PhyWrite );
    xPhyDiscover( &xPhyObject );
    xPhyConfigure( &xPhyObject, &xPHYProperties );
}

/**
 * @brief Initialize Rx/Tx DMA descriptors.
 *
 * @param[in] pxEthDev: Pointer to the DwEqosDev structure.
 */
static void prvInitDescriptors( DwEqosDev * pxEthDev )
{
    pxEthDev->TxDescs = TxDmaDescs;
    pxEthDev->RxDescs = RxDmaDescs;

    pxEthDev->pxRxBufferDescs = RxBufferDescs;

    prvInitRxDescs( pxEthDev );
    prvInitTxDescs( pxEthDev );
}

/**
 * @brief Initialize the Ethernet MAC hardware.
 *
 * @param[in] pxEthDev: Pointer to the DwEqosDev structure.
 */
static BaseType_t prvEqosHwInit( DwEqosDev * pxEthDev )
{
    uint32_t ulVal;
    uint32_t ulTimeout = 100;

    #ifdef EQOS_MTL_HAS_MULTIPLE_QUEUES
        uint32_t ulTxFifoSz, ulRxFifoSz, ulTqs, ulRqs;
    #endif

    /* Soft reset the logic */
    pxEthDev->pxRegs->DMA_BUS_MODE |= DMA_BUS_MODE_SFT_RESET;

    do
    {
        vTaskDelay( pdMS_TO_TICKS( 1 ) );
        ulTimeout--;
    } while( ( pxEthDev->pxRegs->DMA_BUS_MODE & DMA_BUS_MODE_SFT_RESET ) && ulTimeout );

    if ( !ulTimeout )
    {
        /* The DMA soft reset only completes once every clock domain is live,
         * so this is the signature of a missing RMII REF_CLK rather than a
         * link or PHY problem. */
        printf( "ETH DMA reset timeout - no RMII REF_CLK\n" );
        return pdFAIL;
    }

    /* Configure MTL Tx Q0 Operating mode */
    pxEthDev->pxRegs->MTL_TXQ0_OP_MODE &= ~MTL_OP_MODE_TXQEN_MASK;
    pxEthDev->pxRegs->MTL_TXQ0_OP_MODE |= MTL_OP_MODE_TXQEN | MTL_OP_MODE_TSF;

    /* Configure MTL RX Q0 operating mode */
    pxEthDev->pxRegs->MTL_RXQ0_OP_MODE |= (MTL_OP_MODE_RSF |
                                    MTL_OP_MODE_FEP |
                                    MTL_OP_MODE_FUP);
    #ifdef EQOS_MTL_HAS_MULTIPLE_QUEUES
        /*
         *  configure the MTL T/Rx Q0 sizes by finding out the configured
         * Tx RX FIFO sizes. Note that this is not needed if the IP is
         * configured to have only one queue (each for Tx and Rx).
         */

        ulVal = dev->pxRegs->MAC_HW_FEATURE_1;

        ulTxFifoSz = ( ulVal >> EQOS_MAC_HW_FEATURE1_TXFIFOSIZE_SHIFT ) &
                    EQOS_MAC_HW_FEATURE1_TXFIFOSIZE_MASK;

        ulRxFifoSz = ( ulVal >> EQOS_MAC_HW_FEATURE1_RXFIFOSIZE_SHIFT ) &
                    EQOS_MAC_HW_FEATURE1_RXFIFOSIZE_MASK;

        /*
         * FIFO sizes are encoded as log2(fifo_size) - 7 in the above field
         * and tqs and rqs needs to be programmed in blocks of 256 bytes.
         */

        ulTqs = ( 128 << ulTxFifoSz ) / 256 - 1;
        ulRqs = ( 128 << ulRxFifoSz ) / 256 - 1;

        pxEthDev->pxRegs->MTL_TXQ0_OP_MODE &= ~(MTL_TXQ0_OPERATION_MODE_TQS_MASK <<
                                            MTL_TXQ0_OPERATION_MODE_TQS_SHIFT);
        pxEthDev->pxRegs->MTL_TXQ0_OP_MODE |= (tqs <<  MTL_TXQ0_OPERATION_MODE_TQS_SHIFT);

        pxEthDev->pxRegs->MTL_RXQ0_OP_MODE &= ~(EQOS_MTL_RXQ0_OPERATION_MODE_RQS_MASK <<
                                            MTL_TXQ0_OPERATION_MODE_TQS_SHIFT);
        pxEthDev->pxRegs->MTL_RXQ0_OP_MODE |= (rqs << MTL_TXQ0_OPERATION_MODE_TQS_SHIFT);
    #endif

    /* Enable MAC RXQ */
    pxEthDev->pxRegs->MAC_RXQ_CTRL_0 &= ~(EQOS_MAC_RXQ_CTRL0_RXQ0EN_MASK <<
                                        EQOS_MAC_RXQ_CTRL0_RXQ0EN_SHIFT);
    pxEthDev->pxRegs->MAC_RXQ_CTRL_0 |= (EQOS_MAC_RXQ_CTRL0_RXQ0EN_ENABLED_DCB <<
                                        EQOS_MAC_RXQ_CTRL0_RXQ0EN_SHIFT);

    /* Configure RXQ control1 for routing multicast/broadcast queues
     * Note that by default, Q0 will be used.
     */
    pxEthDev->pxRegs->MAC_RXQ_CTRL_1 |= EQOS_MAC_RXQCTRL_MCBCQEN;
    /* Configure tx and rx flow control */

    pxEthDev->pxRegs->MAC_Q0_TX_FLOW_CTRL |= 0xffff << EQOS_MAC_Q0_TX_FLOW_CTRL_PT_SHIFT |
                                      EQOS_MAC_Q0_TX_FLOW_CTRL_TFE;
    pxEthDev->pxRegs->MAC_RX_FLOW_CTRL |= EQOS_MAC_RX_FLOW_CTRL_RFE;

    ulVal = pxEthDev->pxRegs->MAC_CONFIG;
    ulVal &= ~EQOS_MAC_CONFIG_JE;
    ulVal |= ( EQOS_MAC_CONFIG_PS | EQOS_MAC_CONFIG_FES | EQOS_MAC_CONFIG_DM |
               EQOS_MAC_CONFIG_ACS | EQOS_MAC_CONFIG_CST );
    #if ( ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM != 0 )
        ulVal |= EQOS_MAC_CONFIG_IPC;
    #endif
    pxEthDev->pxRegs->MAC_CONFIG = ulVal;

    pxEthDev->pxRegs->MAC_PACKET_FILTER |= ( EQOS_MAC_PACKET_FILTER_PM |
                                             EQOS_MAC_PACKET_FILTER_PR |
                                             EQOS_MAC_PACKET_FILTER_RA );
    /* Configure the DMA block */
    pxEthDev->pxRegs->DMA_CH0_TX_CTRL |= (16 << EQOS_DMA_CH0_TX_CONTROL_TXPBL_SHIFT);
    pxEthDev->pxRegs->DMA_CH0_TX_CTRL &= ~EQOS_DMA_CH0_TX_CONTROL_OSP;

    pxEthDev->pxRegs->DMA_CH0_RX_CTRL |= ((16 << EQOS_DMA_CH0_RX_CONTROL_RXPBL_SHIFT) |
                                   (ETH_BUF_SIZE << EQOS_DMA_CH0_RX_CONTROL_RBSZ_SHIFT));

    ulVal = pxEthDev->pxRegs->DMA_SYS_BUS_MODE;;
    ulVal |= EQOS_DMA_SYSBUS_MODE_BLEN4 | EQOS_DMA_SYSBUS_MODE_BLEN8 |
            EQOS_DMA_SYSBUS_MODE_BLEN16;

    ulVal |= 3 << EQOS_DMA_SYSBUS_MODE_RD_OSR_LMT_SHIFT;
    ulVal |= 1 << EQOS_DMA_SYSBUS_MODE_WR_OSR_LMT_SHIFT;
    ulVal |= EQOS_DMA_SYSBUS_MODE_ONEKBBE;

    pxEthDev->pxRegs->DMA_SYS_BUS_MODE = ulVal;

    prvInitDescriptors( pxEthDev );

    prvSetMacAddr( pxEthDev, ucMACAddress );

    /* Enable DMA Channel 0 interrupts, rx and tx */
    pxEthDev->pxRegs->DMA_CH0_INT_ENABLE |= DMA_CHAN_INTR_ENA_RIE | DMA_CHAN_INTR_ENA_NIE |
        DMA_CHAN_INTR_ENA_TIE | DMA_CHAN_INTR_ENA_AIE | DMA_CHAN_INTR_ENA_RBUE;

    pxEthDev->pxRegs->DMA_CH0_TX_CTRL |= EQOS_DMA_CH0_TX_CONTROL_ST;
    pxEthDev->pxRegs->DMA_CH0_RX_CTRL |= EQOS_DMA_CH0_RX_CONTROL_SR;

    pxEthDev->pxRegs->MAC_CONFIG |= ( EQOS_MAC_CONFIG_RE | EQOS_MAC_CONFIG_TE );

    return pdPASS;
}

/**
 * @brief Update Ethernet MAC speed/duplex settings.
 *
 * Called when a change is observed in the link status and
 * during initial configuration.
 *
 * @param [in] xForce: TRUE/FALSE to force a configuration update.
 */
static void prvEthernetUpdateConfig( BaseType_t xForce )
{
    uint32_t ulDmaChCtrl, ulMacConfig;
    DwEqosDev * pxEthDev = &EQOS0;

    if( ( xForce != pdFALSE ) || ( xPhyObject.ulLinkStatusMask != 0ul ) )
    {
        uint32_t ulConfig;

        ulConfig = pxEthDev->pxRegs->MAC_CONFIG;
        ulConfig &= ~( EQOS_MAC_CONFIG_FES | EQOS_MAC_CONFIG_DM );
        ulConfig |= EQOS_MAC_CONFIG_PS | EQOS_MAC_CONFIG_ACS | EQOS_MAC_CONFIG_CST;

        /* Either the initial configuration or the link is up again */
        if( EQOS0.Config.ucAutoNegCtrl == AN_ENABLE )
        {
 		    xPhyStartAutoNegotiation( &xPhyObject, xPhyGetMask( &xPhyObject ) );

            /*
             * Configure the MAC with the Duplex Mode fixed by the
             * auto-negotiation.
             */
            if( xPhyObject.xPhyProperties.ucDuplex == PHY_DUPLEX_FULL )
            {
                ulConfig |= EQOS_MAC_CONFIG_DM;
            }
            else
            {
                /* Half Duplex, Nothing to do here as we have cleared DM in ulConfig */
            }

            /*
             * Configure the MAC with the speed fixed by the
             * auto-negotiation.
             */
            if( xPhyObject.xPhyProperties.ucSpeed == PHY_SPEED_10 )
            {
                /* Nothing to do here as we have FES cleared in ulConfig */
            }
            else
            {
                    /* Speed 100Mbps */
                    ulConfig |= EQOS_MAC_CONFIG_FES;
            }
        }
        else /* AutoNeg Disabled */
        {
            if( EQOS0.Config.ucDuplex == ETH_DUPLEX_HALF )
            {
                xPhyObject.xPhyPreferences.ucDuplex = PHY_DUPLEX_HALF;
            }
            else
            {
                xPhyObject.xPhyPreferences.ucDuplex = PHY_DUPLEX_FULL;
                ulConfig |= EQOS_MAC_CONFIG_DM;
            }

            if( EQOS0.Config.ucSpeed == ETH_SPEED_10M )
            {
                xPhyObject.xPhyPreferences.ucSpeed = PHY_SPEED_10;
            }
            else
            {
                xPhyObject.xPhyPreferences.ucSpeed = PHY_SPEED_100;
                ulConfig |= EQOS_MAC_CONFIG_FES;
            }

            xPhyObject.xPhyPreferences.ucMDI_X = PHY_MDIX_AUTO;

            /* Use fixed configuration. */
            xPhyFixedValue( &xPhyObject, xPhyGetMask( &xPhyObject ) );
        }

        /* Update MAC configuration and keep Tx/Rx running after AN. */
        pxEthDev->pxRegs->MAC_CONFIG = ulConfig;
        pxEthDev->pxRegs->DMA_CH0_TX_CTRL |= DMA_CONTROL_ST;
        pxEthDev->pxRegs->DMA_CH0_RX_CTRL |= DMA_CONTROL_SR;
        pxEthDev->pxRegs->MAC_CONFIG |= ( EQOS_MAC_CONFIG_TE | EQOS_MAC_CONFIG_RE );
    }
    else
    {
        /* Keep MAC Rx/Tx running. A single BMSR miss used to clear RE/TE
         * and made ping impossible while the RJ45 LED stayed on. */
        ( void ) ulMacConfig;
        ( void ) ulDmaChCtrl;
    }
}

/**
 * @brief Send an Rx Event to the FreeRTOS IP task.
 *
 * @param[in] pxDescriptor: Pointer to the buffer descriptor containing the received packet.
 */
static void prvPassEthMessages( NetworkBufferDescriptor_t * pxDescriptor )
{
    IPStackEvent_t xRxEvent;

    pxDescriptor->pxInterface = FreeRTOS_FirstNetworkInterface();
    if( pxDescriptor->pxEndPoint == NULL )
    {
        pxDescriptor->pxEndPoint = FreeRTOS_MatchingEndpoint( pxDescriptor->pxInterface,
                                                              pxDescriptor->pucEthernetBuffer );
    }
    if( pxDescriptor->pxEndPoint == NULL )
    {
        pxDescriptor->pxEndPoint = FreeRTOS_FirstEndPoint( pxDescriptor->pxInterface );
    }

    xRxEvent.eEventType = eNetworkRxEvent;
    xRxEvent.pvData = ( void * ) pxDescriptor;

    if( xSendEventStructToIPTask( &xRxEvent, ( TickType_t ) 1000 ) != pdPASS )
    {
        vReleaseNetworkBufferAndDescriptor( pxDescriptor );
        iptraceETHERNET_RX_EVENT_LOST();
    }
    else
    {
        iptraceNETWORK_INTERFACE_RECEIVE();
    }
}

/**
 * @brief Recieve a packet from the DMA buffers.
 *
 */
static BaseType_t prvNetworkInterfaceInput( void )
{
    const TickType_t xDescriptorWaitTime = 0;
    uint32_t ulCurIdx;
    DwEqosDev * pxEthDev = &EQOS0;
    DmaDesc * pxDesc;
    BaseType_t xReceivedLength;
    BaseType_t xGotPacket = pdFALSE;
    NetworkBufferDescriptor_t * pxNewDescriptor = NULL, *pxCurDescriptor;
    uint8_t * pucBuffer;

    ulCurIdx = pxEthDev->ulCurRxDescId;
    pxDesc = &pxEthDev->RxDescs[ ulCurIdx ];
    prvDCacheInvalidate( pxDesc, sizeof( DmaDesc ) );

    while( ! ( pxDesc->ulDes3 & RDES3_OWN ) )
	{
        xGotPacket = pdTRUE;
        ulCurIdx = pxEthDev->ulCurRxDescId;
        if( ( pxDesc->ulDes3 & RDES3_ERROR_SUMMARY ) != 0 )
        {
            xReceivedLength = 0;
        }
        else
        {
            /* ACS/CST strips FCS; PL is the payload length. */
            xReceivedLength = ( int32_t ) ( pxDesc->ulDes3 & 0x7fff );
        }

        /* Reject only frames the hardware flagged or that are too short to
         * hold an Ethernet header. The IP stack discards protocols it was not
         * built for, so filtering on ethertype here only cost valid traffic. */
        if( xReceivedLength < 14 )
        {
            #if ( ipconfigZERO_COPY_RX_DRIVER != 0 )
                pxCurDescriptor = pxEthDev->pxRxBufferDescs[ ulCurIdx ];
                pxDesc->ulDes0 = ( uint32_t ) LocalToGlobal( pxCurDescriptor->pucEthernetBuffer );
            #else
                pxDesc->ulDes0 = ( uint32_t ) LocalToGlobal( &RxBuffers[ ulCurIdx ][ 0 ] );
            #endif
            pxDesc->ulDes3 = RDES3_OWN | RDES3_INT_ON_COMPLETION_EN | RDES3_BUFFER1_VALID_ADDR;
            prvDCacheClean( pxDesc, sizeof( DmaDesc ) );
            pxEthDev->pxRegs->DMA_CH0_RX_END_ADDR = ( uint32_t ) LocalToGlobal( &( pxEthDev->RxDescs[ ulCurIdx ] ) );
            pxEthDev->ulCurRxDescId++;
            pxEthDev->ulCurRxDescId %= RX_DESC_COUNT;
            pxDesc = &pxEthDev->RxDescs[ pxEthDev->ulCurRxDescId ];
            prvDCacheInvalidate( pxDesc, sizeof( DmaDesc ) );
            continue;
        }

        #if ( ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM != 0 )
            if ( ( pxDesc->ulDes1 & RDES1_IP_HDR_ERROR ) || ( pxDesc->ulDes1 & RDES1_IP_CSUM_ERROR ) )
            {
                /* There are checksum errors in this frame, do not forward to IP, just refresh the descriptor */
                #if ( ipconfigZERO_COPY_RX_DRIVER != 0 )
                    /* Find out the NetworkDescriptor associated with this DMA descriptor */
                    pxCurDescriptor = pxEthDev->pxRxBufferDescs[ ulCurIdx ];
                    pxDesc->ulDes0 = ( uint32_t ) LocalToGlobal( pxCurDescriptor->pucEthernetBuffer );
                #else
                    pxDesc->ulDes0 = ( uint32_t ) LocalToGlobal( &RxBuffers[ ulCurIdx ][ 0 ] );
                #endif
                pxDesc->ulDes3 = RDES3_OWN | RDES3_INT_ON_COMPLETION_EN | RDES3_BUFFER1_VALID_ADDR;

                prvDCacheClean( pxDesc, sizeof( DmaDesc ) );

                pxEthDev->pxRegs->DMA_CH0_RX_END_ADDR = ( uint32_t ) LocalToGlobal( &( pxEthDev->RxDescs[ ulCurIdx ] ) );
                pxEthDev->ulCurRxDescId++;
                pxEthDev->ulCurRxDescId %= RX_DESC_COUNT;
                pxDesc = &pxEthDev->RxDescs[ pxEthDev->ulCurRxDescId ];

                /* continue processing any pending DMA descriptors */
                continue;
            }
        #endif

        pxNewDescriptor = pxGetNetworkBufferWithDescriptor( ETH_BUF_SIZE, xDescriptorWaitTime );

        if ( pxNewDescriptor != NULL )
        {
            #if ( ipconfigZERO_COPY_RX_DRIVER != 0 )
                /* Find out the NetworkDescriptor associated with this DMA descriptor */
                pxCurDescriptor = pxEthDev->pxRxBufferDescs[ ulCurIdx ];
                prvDCacheInvalidate( pxCurDescriptor->pucEthernetBuffer, ETH_BUF_SIZE );
                configASSERT( pxCurDescriptor != NULL );
            #else
                pucBuffer = ( uint8_t * ) &RxBuffers[ ulCurIdx ][ 0 ];
                prvDCacheInvalidate( pucBuffer, ETH_BUF_SIZE );
                pxCurDescriptor = pxNewDescriptor;
                memcpy( pxNewDescriptor->pucEthernetBuffer, pucBuffer, xReceivedLength );
            #endif

            pxCurDescriptor->xDataLength = xReceivedLength;

            prvPassEthMessages( pxCurDescriptor );
        }
        else
        {
            /* Buffer Allocation failed, use the old buffer to refresh the descriptor
             * if zero copy Rx is being used.
             */
            #if ( ipconfigZERO_COPY_RX_DRIVER != 0)
                pxNewDescriptor = pxEthDev->pxRxBufferDescs[ ulCurIdx ];
            #endif
        }

        /* refresh the descriptor */
        #if ( ipconfigZERO_COPY_RX_DRIVER != 0)
            pxDesc->ulDes0 = ( uint32_t ) LocalToGlobal( pxNewDescriptor->pucEthernetBuffer );
            pxEthDev->pxRxBufferDescs[ ulCurIdx ] = pxNewDescriptor;
        #else
            pxDesc->ulDes0 = ( uint32_t ) LocalToGlobal( &RxBuffers[ ulCurIdx ][ 0 ] );
        #endif
        pxDesc->ulDes3 = RDES3_OWN | RDES3_INT_ON_COMPLETION_EN |
                            RDES3_BUFFER1_VALID_ADDR;

        prvDCacheClean( &pxEthDev->RxDescs[ ulCurIdx ], sizeof( DmaDesc ) );

        pxEthDev->pxRegs->DMA_CH0_RX_END_ADDR = ( uint32_t ) LocalToGlobal( &( pxEthDev->RxDescs[ ulCurIdx ] ) );
        pxEthDev->ulCurRxDescId++;
        pxEthDev->ulCurRxDescId %= RX_DESC_COUNT;
        pxDesc = &pxEthDev->RxDescs[ pxEthDev->ulCurRxDescId ];
        prvDCacheInvalidate( pxDesc, sizeof( DmaDesc ) );
    }


    if (ulRbuFlag)
    {
        /* Restart Rx */
        pxEthDev->pxRegs->DMA_CH0_RX_CTRL |= EQOS_DMA_CH0_RX_CONTROL_SR;
        pxEthDev->pxRegs->MAC_CONFIG |= EQOS_MAC_CONFIG_RE;

        ulRbuFlag = 0;
    }

    return xGotPacket;
}

static uint32_t ulTxDescClearIdx;

/**
 * @brief Free the Network buffer and descriptor used for Tx.
 *
 * Free as many Network buffers and descriptor as possible used during Tx if zero copy
 * Tx is being used. Release a Tx Descritptor semaphore for each free (non-'OWN'ed)
 * DMA descriptor.
 */
static void vClearTXBuffers()
{
    DmaDesc *pxDesc;
    DwEqosDev *pxEthDev = &EQOS0;

    #if ( ipconfigZERO_COPY_TX_DRIVER != 0 )
        NetworkBufferDescriptor_t * pxNetworkBuffer;
        uint8_t * ucPayLoad;
    #endif

    size_t uxCount;
    uint32_t ulCurIdx;

    if( xTXDescriptorSemaphore == NULL )
    {
        return;
    }

    taskENTER_CRITICAL();

    uxCount = ( ( UBaseType_t ) TX_DESC_COUNT ) - uxSemaphoreGetCount( xTXDescriptorSemaphore );
    ulCurIdx = pxEthDev->ulCurTxDescId;
    pxDesc = &pxEthDev->TxDescs[ ulTxDescClearIdx ];
    prvDCacheInvalidate( pxDesc, sizeof( DmaDesc ) );

    /* Do not stop when clear==cur: that is also the "ring full" case
     * (12 outstanding, index wrapped) and it leaked every TX descriptor. */
    while( uxCount > 0 )
    {
        if( ( pxDesc->ulDes3 & TDES3_OWN ) != 0 )
        {
            break;
        }
        #if ( ipconfigZERO_COPY_TX_DRIVER != 0 )
        {
            ucPayLoad = ( uint8_t * ) GlobalToLocal( pxDesc->ulDes0 );

            if( ucPayLoad != NULL )
            {
                pxNetworkBuffer = pxPacketBuffer_to_NetworkBuffer( ucPayLoad );

                if( pxNetworkBuffer != NULL )
                {
                    vReleaseNetworkBufferAndDescriptor( pxNetworkBuffer );
                }
            }
        }
        #endif /* ipconfigZERO_COPY_TX_DRIVER */

        xSemaphoreGive( xTXDescriptorSemaphore );
        uxCount--;
        ulTxDescClearIdx++;
        ulTxDescClearIdx %= TX_DESC_COUNT;
        pxDesc = &pxEthDev->TxDescs[ ulTxDescClearIdx ];
        prvDCacheInvalidate( pxDesc, sizeof( DmaDesc ) );
    }

    ( void ) ulCurIdx;
    taskEXIT_CRITICAL();
}

/**
 * @brief Task function that handles all the events signalled by the interrupt handler.
 *
 * The task processes the Rx and Tx complete events signalled by the DMA interrupts.
 * It also monitors the resource usage statistics and the link status.
 *
 * @param[in] pvParameters: Unused
 */
static void prvEqosHandlerTask( void * pvParameters )
{
    BaseType_t xResult;
    const TickType_t ulMaxBlockTime = pdMS_TO_TICKS( 2UL );

    ( void ) pvParameters;

    for( ; ; )
    {
        xResult = 0;

        if( ( ulISREvents & EQOS_ALL_EVENT ) == 0 )
        {
            ulTaskNotifyTake( pdFALSE, ulMaxBlockTime );
        }

        xResult = prvNetworkInterfaceInput();
        ulISREvents &= ~EQOS_RX_EVENT;
        ulISREvents &= ~EQOS_TX_EVENT;
        vClearTXBuffers();

        if( xPhyCheckLinkStatus( &xPhyObject, xResult ) != 0 )
        {
            prvEthernetUpdateConfig( pdFALSE );
        }
    }
}

static BaseType_t prvPinMuxConfigure( void )
{
    int32_t ret;

    ret = pinconf_set( PORT_11, PIN_0, PINMUX_ALTERNATE_FUNCTION_6,
                       PADCTRL_READ_ENABLE | PADCTRL_OUTPUT_DRIVE_STRENGTH_4MA );
    if (ret)
        return pdFAIL;

    ret = pinconf_set( PORT_11, PIN_1, PINMUX_ALTERNATE_FUNCTION_5, PADCTRL_READ_ENABLE );
    if (ret)
        return pdFAIL;

    ret = pinconf_set( PORT_11, PIN_2, PINMUX_ALTERNATE_FUNCTION_6, 0 );
    if (ret)
        return pdFAIL;

    ret = pinconf_set( PORT_11, PIN_3, PINMUX_ALTERNATE_FUNCTION_6, PADCTRL_READ_ENABLE );
    if (ret)
        return pdFAIL;

    ret = pinconf_set( PORT_11, PIN_4, PINMUX_ALTERNATE_FUNCTION_6, PADCTRL_READ_ENABLE );
    if (ret)
        return pdFAIL;

    ret = pinconf_set( PORT_11, PIN_5, PINMUX_ALTERNATE_FUNCTION_6, PADCTRL_READ_ENABLE );
    if (ret)
        return pdFAIL;

    /* P11_6 is ETH_RST_B. AF6 ETH_RST holds the RTL8201 in reset on AppKit.
     * Leave it as GPIO driven high by vAppEthPhyHoldOutOfReset(). */

    ret = pinconf_set( PORT_11, PIN_7, PINMUX_ALTERNATE_FUNCTION_6, PADCTRL_READ_ENABLE );
    if (ret)
        return pdFAIL;

    ret = pinconf_set( PORT_6, PIN_0, PINMUX_ALTERNATE_FUNCTION_6,
                       PADCTRL_SLEW_RATE_FAST | PADCTRL_OUTPUT_DRIVE_STRENGTH_8MA );
    if (ret)
        return pdFAIL;

    ret = pinconf_set( PORT_10, PIN_5, PINMUX_ALTERNATE_FUNCTION_6,
                       PADCTRL_SLEW_RATE_FAST | PADCTRL_OUTPUT_DRIVE_STRENGTH_8MA );
    if (ret)
        return pdFAIL;

    ret = pinconf_set( PORT_10, PIN_6, PINMUX_ALTERNATE_FUNCTION_6,
                       PADCTRL_SLEW_RATE_FAST | PADCTRL_OUTPUT_DRIVE_STRENGTH_8MA );
    if (ret)
        return pdFAIL;

    return pdPASS;
}

/**
 * @brief Initialise the Network Interface.
 *
 * Initialise the MAC hardware and DMA descriptors. Also, probe for and configure
 * the PHYs that are available in the system. Create the FreeRTOS task that handles
 * the events signalled by the interrupt handler and create the counting semaphore
 * used to synchronize/manage the Tx DMA descriptor usage.
 *
 * @return pdPASS, if HW initialisation was successful and a link could be detected. Else pdFALSE.
 */
BaseType_t xNetworkInterfaceInitialise( void )
{
    BaseType_t xReturn = pdPASS;
    static uint8_t ucHwInitDone = 0;

    if( !ucHwInitDone )
    {
	    xReturn = prvPinMuxConfigure();

        if ( xReturn != pdPASS )
            return xReturn;

        enable_eth_periph_clk();

        xReturn = prvEqosHwInit( &EQOS0 );

        if ( xReturn != pdPASS )
            return xReturn;

        prvPhyInit();

        ucHwInitDone = 1;
    }

    prvEthernetUpdateConfig( pdTRUE );

    if( xTXDescriptorSemaphore == NULL )
    {
        xTXDescriptorSemaphore = xSemaphoreCreateCounting( ( UBaseType_t ) TX_DESC_COUNT,
                                                                 ( UBaseType_t ) TX_DESC_COUNT );
    }

    /* Must be below the IP task. Pack used configMAX_PRIORITIES-1 with a
     * 140-word stack, which preempted init and overflowed. */
    if( xRxHandlerTask == NULL )
    {
        xReturn = xTaskCreate( prvEqosHandlerTask, "EQOS_MAC", HANDLER_TASK_STACK_SIZE, NULL,
                               ipconfigIP_TASK_PRIORITY - 1, &xRxHandlerTask );
    }

    vTaskSetTimeOutState( &xPhyObject.xLinkStatusTimer );
    xPhyObject.xLinkStatusRemaining = pdMS_TO_TICKS( 15000 );

    NVIC_ClearPendingIRQ( EQOS0.xIrq );
    NVIC_SetPriority( EQOS0.xIrq, 16 );
    NVIC_EnableIRQ( EQOS0.xIrq );
    EQOS0.pxRegs->DMA_CH0_RX_END_ADDR =
        ( uint32_t ) LocalToGlobal( &( EQOS0.RxDescs[ RX_DESC_COUNT - 1 ] ) );

    if( xPhyObject.ulLinkStatusMask != 0ul )
    {
        xReturn = pdPASS;
    }
    else
    {
        xReturn = pdFAIL;
    }

    return xReturn;
}

/**
 * @brief Transmit a network packet.
 *
 * @param[in] pxNetworkBuffer: Descriptor containing the packet to be sent.
 * @param[in] xReleaseAfterSend: TRUE if the buffer and descriptor needs to be freed after Tx. Else FALSE.
 * @return pdPASS, if the transmission was successful. Else pdFALSE.
 */
BaseType_t xNetworkInterfaceOutput( NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                        BaseType_t xReleaseAfterSend )
{
    BaseType_t xReturn = pdFAIL;
    uint32_t ulTransmitSize = 0, ulCurIdx;
    DmaDesc *pxDesc;
    DwEqosDev *pxEthDev = &EQOS0;

    /* maximum time to block for a free Tx descriptor */
    const TickType_t xBlockTimeTicks = pdMS_TO_TICKS( 2u );

    do {
        vClearTXBuffers();

        /* Do not gate TX on ulLinkStatusMask. BMSR is latching-low and a
         * single MDIO glitch used to drop ICMP replies while the LED stayed on. */
        {
            if( xSemaphoreTake( xTXDescriptorSemaphore, xBlockTimeTicks ) != pdPASS )
            {
                break;
			}

            ulCurIdx = pxEthDev->ulCurTxDescId;
            pxDesc = &pxEthDev->TxDescs[ ulCurIdx ];
            prvDCacheInvalidate( pxDesc, sizeof( DmaDesc ) );
            if( ( pxDesc->ulDes3 & TDES3_OWN ) != 0 )
            {
                xSemaphoreGive( xTXDescriptorSemaphore );
                break;
            }

            ulTransmitSize = pxNetworkBuffer->xDataLength;

            if ( ulTransmitSize > ETH_BUF_SIZE )
            {
                ulTransmitSize = ETH_BUF_SIZE;
            }

            pxDesc->ulDes2 = TDES2_INTERRUPT_ON_COMPLETION | ulTransmitSize;
            #if ( ipconfigZERO_COPY_TX_DRIVER == 0 )
            {
                uint8_t * pucTx = ( uint8_t * ) &TxBuffers[ ulCurIdx ][ 0 ];

                memset( pucTx, 0, 60u );
                memcpy( pucTx, pxNetworkBuffer->pucEthernetBuffer, ulTransmitSize );
                if( ulTransmitSize < 60u )
                {
                    ulTransmitSize = 60u;
                    pxDesc->ulDes2 = TDES2_INTERRUPT_ON_COMPLETION | ulTransmitSize;
                }
                pxDesc->ulDes0 = ( uint32_t ) LocalToGlobal( pucTx );
                prvDCacheClean( pucTx, ETH_BUF_SIZE );
            }
            #else
            {
                configASSERT( xReleaseAfterSend != 0 );
                pxDesc->ulDes0 = ( uint32_t ) LocalToGlobal( pxNetworkBuffer->pucEthernetBuffer );
                prvDCacheClean( pxNetworkBuffer->pucEthernetBuffer, ETH_BUF_SIZE );

                /* The Buffer has been taken over by the DMA, do not release it */
                xReleaseAfterSend = pdFALSE_UNSIGNED;
            }
            #endif


            pxEthDev->ulCurTxDescId++;
            pxEthDev->ulCurTxDescId %= TX_DESC_COUNT;

            pxDesc->ulDes3 = TDES3_OWN | TDES3_LAST_DESCRIPTOR | TDES3_FIRST_DESCRIPTOR |
                            ulTransmitSize;
            #if ( ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM != 0 )
                pxDesc->ulDes3 |= (TX_CIC_FULL << TDES3_CHECKSUM_INSERTION_SHIFT);
            #endif

            prvDCacheClean( pxDesc, sizeof( DmaDesc ) );
            __DSB();

            pxEthDev->pxRegs->DMA_CH0_STATUS =
                DMA_CHAN_STATUS_TI | DMA_CHAN_STATUS_TBU | DMA_CHAN_STATUS_NIS;
            pxEthDev->pxRegs->DMA_CH0_TX_CTRL |= EQOS_DMA_CH0_TX_CONTROL_ST;
            pxEthDev->pxRegs->DMA_CH0_TX_END_ADDR = ( uint32_t ) LocalToGlobal( &( pxEthDev->TxDescs[ pxEthDev->ulCurTxDescId ] ) );
            xReturn = pdPASS;
        }
    } while( 0 );


    if( xReleaseAfterSend != pdFALSE )
    {
        vReleaseNetworkBufferAndDescriptor( pxNetworkBuffer );
    }

    return xReturn;
}

/*-----------------------------------------------------------*/
/* Used with BufferAllocation_1 strategy */
#define NUMBUF	ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS
/**@brief Buffer area used with BufferAllocation_1.c */
static uint8_t ucNetworkPackets[ NUMBUF * ETH_BUF_SIZE ] __attribute__((aligned(32))) __attribute__((section("eth_buf")));
/**
 * @brief Allocate packet buffer area to descriptors. Used with BufferAllocation_1 strategy.
 *
 * @param[in] pxNetworkBuffers: Array of NetworkBuffer descriptors.
 */
void vNetworkInterfaceAllocateRAMToBuffers( NetworkBufferDescriptor_t pxNetworkBuffers[ ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS ] )
{

    uint8_t * ucRAMBuffer = ucNetworkPackets;
    uint32_t ul;

    for( ul = 0; ul < NUMBUF; ul++ )
    {
        pxNetworkBuffers[ ul ].pucEthernetBuffer = ucRAMBuffer + ipBUFFER_PADDING;
        *( ( unsigned * ) ucRAMBuffer ) = ( unsigned ) ( &( pxNetworkBuffers[ ul ] ) );
        ucRAMBuffer += ETH_BUF_SIZE;
    }
}
/*-----------------------------------------------------------*/
