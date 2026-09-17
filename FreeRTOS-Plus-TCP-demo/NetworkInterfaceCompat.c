/**
 * @file NetworkInterfaceCompat.c
 * @brief Adapt the Ensemble V2.3.2 network interface to FreeRTOS+TCP V4 APIs.
 *
 * Also releases the RTL8201 from reset. AppKit-E8 / DevKit-E8 / DevKit-E7 wire
 * nRST to ETH_RST_B (P11_6). The pack driver muxes that pin as ETH_RST, which
 * does not deassert the PHY. Alif's own E8 examples remux it as GPIO and drive
 * it high before MDIO.
 */

#include <stdio.h>
#include <string.h>

#include "RTE_Components.h"
#include CMSIS_device_header

#include "FreeRTOS.h"
#include "task.h"
#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_Routing.h"
#include "NetworkInterface.h"
#include "NetworkBufferManagement.h"
#include "phyHandling.h"
#include "pinconf.h"
#include "Driver_IO.h"

#ifndef ETH_BUF_SIZE
#define ETH_BUF_SIZE    1536
#endif

extern BaseType_t xNetworkInterfaceInitialise( void );
extern BaseType_t xNetworkInterfaceOutput( NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                           BaseType_t xReleaseAfterSend );
extern void vNetworkInterfaceAllocateRAMToBuffers( NetworkBufferDescriptor_t pxNetworkBuffers[ ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS ] );
extern BaseType_t __real_xPhyDiscover( EthernetPhy_t * pxPhyObject );
extern BaseType_t __real_xPhyStartAutoNegotiation( EthernetPhy_t * pxPhyObject,
                                                   uint32_t ulPhyMask );
extern BaseType_t __real_xSendEventStructToIPTask( const IPStackEvent_t * pxEvent,
                                                   TickType_t xTimeout );

static NetworkInterface_t * pxMyInterface = NULL;

extern ARM_DRIVER_GPIO ARM_Driver_GPIO_( 11 );
static ARM_DRIVER_GPIO * const pxGpio11 = &ARM_Driver_GPIO_( 11 );

#define ETH_PHY_RESET_PORT    PORT_11
#define ETH_PHY_RESET_PIN     PIN_6
#define phyBMSR_LINK_STATUS   0x0004U
#define phyREG_01_BMSR        0x01

static void prvFixMdioPads( void )
{
    /* Pack NI pinmux omits the AppKit MDIO pull-up. Without it, the RJ45
     * link LED can still light (PHY auto-negs on its own) while software
     * never sees a PHY on MDIO. */
    pinconf_set( PORT_11, PIN_1, PINMUX_ALTERNATE_FUNCTION_5,
                 PADCTRL_READ_ENABLE | PADCTRL_DRIVER_DISABLED_PULL_UP |
                 PADCTRL_OUTPUT_DRIVE_STRENGTH_4MA );
    pinconf_set( PORT_11, PIN_2, PINMUX_ALTERNATE_FUNCTION_6,
                 PADCTRL_DRIVER_DISABLED_PULL_UP | PADCTRL_OUTPUT_DRIVE_STRENGTH_4MA );
}

void vAppEthPhyHoldOutOfReset( void )
{
    /* Do not pulse nRST low. The pack pinmuxes P11_6 as ETH_RST (AF6), which
     * can leave the PHY in reset; a GPIO low pulse then made the link LED
     * stay off if the high level did not stick. Drive GPIO high only. */
    ( void ) pinconf_set( ETH_PHY_RESET_PORT, ETH_PHY_RESET_PIN,
                          PINMUX_ALTERNATE_FUNCTION_0,
                          PADCTRL_OUTPUT_DRIVE_STRENGTH_4MA );

    ( void ) pxGpio11->Initialize( ETH_PHY_RESET_PIN, NULL );
    ( void ) pxGpio11->PowerControl( ETH_PHY_RESET_PIN, ARM_POWER_FULL );
    ( void ) pxGpio11->SetDirection( ETH_PHY_RESET_PIN, GPIO_PIN_DIRECTION_OUTPUT );
    ( void ) pxGpio11->SetValue( ETH_PHY_RESET_PIN, GPIO_PIN_OUTPUT_STATE_HIGH );
}

BaseType_t __wrap_xPhyDiscover( EthernetPhy_t * pxPhyObject )
{
    BaseType_t xCount;

    /* Pack pinmux just set P11_6 back to ETH_RST AF6. Take nRST high again. */
    vAppEthPhyHoldOutOfReset();
    prvFixMdioPads();
    if( xTaskGetSchedulerState() != taskSCHEDULER_NOT_STARTED )
    {
        vTaskDelay( pdMS_TO_TICKS( 100 ) );
    }
    xCount = __real_xPhyDiscover( pxPhyObject );

    /* MDIO often echoes the same RTL8201 at addr 0 and 1. Dual reset/AN
     * then leaves the MAC talking to a ghost port. Keep one PHY. */
    if( ( pxPhyObject->xPortCount >= 2 ) &&
        ( pxPhyObject->ulPhyIDs[ 0 ] == pxPhyObject->ulPhyIDs[ 1 ] ) )
    {
        pxPhyObject->xPortCount = 1;
        pxPhyObject->ulPhyIDs[ 1 ] = 0;
        xCount = 1;
    }

    /* RTL8201: page 7 RMSR — RMII mode, and CLKDIR (bit12) left at 0 so the
     * PHY drives 50 MHz out of CLKOUT into the SoC ETH_REFCLK pin. The MAC
     * must select that pin via ETH_CTRL0 RMII_CLKSEL=0 to stay in sync. */
    if( ( pxPhyObject->xPortCount > 0 ) && ( pxPhyObject->fnPhyWrite != NULL ) &&
        ( pxPhyObject->fnPhyRead != NULL ) )
    {
        uint32_t ulRmsr = 0;
        BaseType_t xAddr = pxPhyObject->ucPhyIndexes[ 0 ];

        ( void ) pxPhyObject->fnPhyWrite( xAddr, 0x1F, 7U );
        ( void ) pxPhyObject->fnPhyRead( xAddr, 0x10, &ulRmsr );
        /* Linux rtl8201_config_init: RMII + RX delay 0x4 + TX delay 0x5.
         * Default timing 0xF left RX working and TX CRC-garbled on the wire. */
        ulRmsr &= ~( ( 0xFu << 4 ) | ( 0xFu << 8 ) | ( 1u << 12 ) );
        /* RX delay 0xF matched clean LLDP/ARP on this board; Linux TX delay
         * 0x5 is what made replies appear on the wire at all. */
        ulRmsr |= ( 1U << 3 ) | ( 0xFU << 4 ) | ( 0x5U << 8 );
        ( void ) pxPhyObject->fnPhyWrite( xAddr, 0x10, ulRmsr );
        ( void ) pxPhyObject->fnPhyWrite( xAddr, 0x1F, 0U );
    }

    return xCount;
}

BaseType_t __wrap_xPhyStartAutoNegotiation( EthernetPhy_t * pxPhyObject,
                                            uint32_t ulPhyMask )
{
    BaseType_t xReturn;

    if( ( ulPhyMask == 0U ) && ( pxPhyObject->xPortCount > 0 ) )
    {
        ulPhyMask = ( ( ( uint32_t ) 1U ) << pxPhyObject->xPortCount ) - 1U;
    }

    xReturn = __real_xPhyStartAutoNegotiation( pxPhyObject, ulPhyMask );

    if( ( pxPhyObject->ulLinkStatusMask == 0U ) && ( pxPhyObject->xPortCount > 0 ) &&
        ( pxPhyObject->fnPhyRead != NULL ) )
    {
        uint32_t ulBmsr = 0;
        BaseType_t xAddress = pxPhyObject->ucPhyIndexes[ 0 ];

        /* BMSR link is latching-low; read twice for the live state. */
        ( void ) pxPhyObject->fnPhyRead( xAddress, phyREG_01_BMSR, &ulBmsr );
        ( void ) pxPhyObject->fnPhyRead( xAddress, phyREG_01_BMSR, &ulBmsr );
        if( ( ulBmsr & phyBMSR_LINK_STATUS ) != 0U )
        {
            /* PHY linked (LED on) but AN did not fill the mask. Force the
             * MAC to 100/full so initialise can succeed. */
            pxPhyObject->ulLinkStatusMask = 1U;
            pxPhyObject->xPhyProperties.ucSpeed = PHY_SPEED_100;
            pxPhyObject->xPhyProperties.ucDuplex = PHY_DUPLEX_FULL;
        }
    }

    return xReturn;
}

static BaseType_t prvNetworkInterfaceInitialise( NetworkInterface_t * pxInterface )
{
    BaseType_t xReturn;

    ( void ) pxInterface;
    xReturn = xNetworkInterfaceInitialise();
    vAppEthPhyHoldOutOfReset();

    /* Pass multicast already; also accept all unicast so a MAC-filter
     * mismatch cannot swallow ARP/ping while the PHY LED is on. */
    ( ( volatile uint32_t * ) ETH_BASE )[ 2 ] |= ( 1u << 31 ) | 1u;

    if( xReturn != pdPASS )
    {
        printf( "ETH init no link\n" );
    }
    return xReturn;
}

static BaseType_t prvNetworkInterfaceOutput( NetworkInterface_t * pxInterface,
                                            NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                            BaseType_t xReleaseAfterSend )
{
    ( void ) pxInterface;
    return xNetworkInterfaceOutput( pxNetworkBuffer, xReleaseAfterSend );
}

BaseType_t xGetPhyLinkStatus( NetworkInterface_t * pxInterface )
{
    ( void ) pxInterface;
    return pdTRUE;
}

NetworkInterface_t * pxFillInterfaceDescriptor( BaseType_t xEMACIndex,
                                                NetworkInterface_t * pxInterface )
{
    static char pcName[] = "eth0";

    ( void ) xEMACIndex;

    memset( pxInterface, 0, sizeof( *pxInterface ) );
    pxInterface->pcName = pcName;
    pxInterface->pfInitialise = prvNetworkInterfaceInitialise;
    pxInterface->pfOutput = prvNetworkInterfaceOutput;
    pxInterface->pfGetPhyLinkStatus = xGetPhyLinkStatus;
    pxMyInterface = pxInterface;

    FreeRTOS_AddNetworkInterface( pxInterface );

    return pxInterface;
}

BaseType_t __wrap_xSendEventStructToIPTask( const IPStackEvent_t * pxEvent,
                                            TickType_t xTimeout )
{
    if( ( pxEvent != NULL ) && ( pxEvent->eEventType == eNetworkRxEvent ) &&
        ( pxEvent->pvData != NULL ) && ( pxMyInterface != NULL ) )
    {
        NetworkBufferDescriptor_t * pxBuffer =
            ( NetworkBufferDescriptor_t * ) pxEvent->pvData;
        const uint8_t * puc = pxBuffer->pucEthernetBuffer;

        pxBuffer->pxInterface = pxMyInterface;
        if( pxBuffer->pxEndPoint == NULL )
        {
            pxBuffer->pxEndPoint = FreeRTOS_MatchingEndpoint( pxMyInterface, puc );
        }
        if( pxBuffer->pxEndPoint == NULL )
        {
            pxBuffer->pxEndPoint = FreeRTOS_FirstEndPoint( pxMyInterface );
        }
    }

    return __real_xSendEventStructToIPTask( pxEvent, xTimeout );
}

size_t uxNetworkInterfaceAllocateRAMToBuffers( NetworkBufferDescriptor_t pxNetworkBuffers[ ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS ] )
{
    vNetworkInterfaceAllocateRAMToBuffers( pxNetworkBuffers );

    /* V4 BufferAllocation_1.c refuses any request larger than this value.
     * The Ensemble NI (prvInitRxDescs) asks for ETH_BUF_SIZE, not
     * ETH_BUF_SIZE - ipBUFFER_PADDING. Returning the smaller figure made
     * pxGetNetworkBufferWithDescriptor() return NULL and tripped
     * configASSERT( pxBuffer != NULL ). */
    return ( size_t ) ETH_BUF_SIZE;
}
