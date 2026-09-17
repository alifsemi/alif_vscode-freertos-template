/*
 * FreeRTOS+TCP V2.3.2
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * http://aws.amazon.com/freertos
 * http://www.FreeRTOS.org
 */

/**
 * @file main.c
 * @brief FreeRTOS-Plus-TCP demo.
 */

#include <stdio.h>
#include <errno.h>

#include "RTE_Components.h"
#include CMSIS_device_header

#include "SEGGER_RTT.h"
#include "board_config.h"
#include "aipm.h"
#include "sys_ctrl_eth.h"
#include "fault_handler.h"

#include <FreeRTOS.h>
#include "task.h"

#include <FreeRTOSConfig.h>

#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_ARP.h"

/* For demo tasks*/
#include "SimpleTCPEchoServer.h"
#include "SimpleUDPEchoServer.h"

void vAppEthPhyHoldOutOfReset( void );

/* DTCM is 256 KB and was 100% full with the kernel heap in .bss, which
 * UsageFaulted (STKOF) as soon as extra tasks started after IP-up. SRAM0
 * is already powered before the first pvPortMalloc. */
uint8_t ucHeap[ configTOTAL_HEAP_SIZE ] __attribute__( ( section( "eth_buf" ), aligned( 8 ) ) );

/* Echo server task parameters. */
#define mainECHO_SERVER_TASK_STACK_SIZE               ( 512 )
#define mainECHO_SERVER_TASK_PRIORITY                 ( tskIDLE_PRIORITY + 1 )

#define mainUDP_ECHO_SERVER_PORT                      7
/** @brief Used by the pseudo random number generator. */
static UBaseType_t ulNextRand;

/** @brief Local MAC Address */
const uint8_t ucMACAddress[ 6 ] =
{
	configMAC_ADDR0,
    configMAC_ADDR1,
    configMAC_ADDR2,
    configMAC_ADDR3,
    configMAC_ADDR4,
    configMAC_ADDR5
};
/** @brief Local IP address */
static const uint8_t ucIPAddress[ 4 ] =
{
    configIP_ADDR0,
    configIP_ADDR1,
    configIP_ADDR2,
    configIP_ADDR3
};

/** @brief Net mask */
static const uint8_t ucNetMask[ 4 ] =
{
    configNET_MASK0,
    configNET_MASK1,
    configNET_MASK2,
    configNET_MASK3
};

/** @brief Gateway address */
static const uint8_t ucGatewayAddress[ 4 ] =
{
    configGATEWAY_ADDR0,
    configGATEWAY_ADDR1,
    configGATEWAY_ADDR2,
    configGATEWAY_ADDR3
};

/** @brief DNS Server Address */
static const uint8_t ucDNSServerAddress[ 4 ] =
{
    configDNS_SERVER_ADDR0,
    configDNS_SERVER_ADDR1,
    configDNS_SERVER_ADDR2,
    configDNS_SERVER_ADDR3
};

/** @brief Utility function to generate a pseudo random number */
UBaseType_t uxRand( void )
{
    const uint32_t ulMultiplier = 0x015a4e35UL, ulIncrement = 1UL;

    ulNextRand = ( ulMultiplier * ulNextRand ) + ulIncrement;

    return( ( int ) ( ulNextRand ) & 0x7fffUL );
}

/**
 * @brief Get a pseuo random number
 *
 * @param[out] pulNumber: Address to store the random number in
 */
BaseType_t xApplicationGetRandomNumber( uint32_t * pulNumber )
{
    *pulNumber = uxRand();

    return pdTRUE;
}

/**
 * @brief Callback to provide a TCP initial sequence number
 *
 * Callback that provides the inputs necessary to generate a randomized TCP
 * Initial Sequence Number per RFC 6528.  THIS IS ONLY A DUMMY IMPLEMENTATION
 * THAT RETURNS A PSEUDO RANDOM NUMBER SO IS NOT INTENDED FOR USE IN PRODUCTION
 * SYSTEMS.
 *
 */
extern uint32_t ulApplicationGetNextSequenceNumber( uint32_t ulSourceAddress,
                                                    uint16_t usSourcePort,
                                                    uint32_t ulDestinationAddress,
                                                    uint16_t usDestinationPort )
{
	( void ) ulSourceAddress;
	( void ) usSourcePort;
	( void ) ulDestinationAddress;
    ( void ) usDestinationPort;

    return uxRand();
}

/**
 * @brief Function called by FreeRTOS+TCP when network connects/disconnects
 *
 * Defined by the application code, but called by FreeRTOS+TCP when the network
 * connects/disconnects (if ipconfigUSE_NETWORK_EVENT_HOOK is set to 1 in
 * FreeRTOSIPConfig.h).
 *
 * For the demo of the FreeRTOS+TCP, when the network is up, this function creates
 * one TCP echo server and one UDP echo server tasks. It also prints the network
 * address information (IP address, netmask, gateway address etc.).
 */
void vApplicationIPNetworkEventHook( eIPCallbackEvent_t eNetworkEvent )
{
uint32_t ulIPAddress, ulNetMask, ulGatewayAddress, ulDNSServerAddress;
static BaseType_t xTasksAlreadyCreated = pdFALSE;
int8_t cBuffer[ 16 ];

    /* Check this was a network up event, as opposed to a network down event. */
    if( eNetworkEvent == eNetworkUp )
    {
        /* Create the tasks that use the TCP/IP stack if they have not already been
        created. */
        if( xTasksAlreadyCreated == pdFALSE )
        {
            /* Echo servers wait until ping/ARP work; they overflowed DTCM. */
            xTasksAlreadyCreated = pdTRUE;
        }

        /* The network is up and configured.  Print out the configuration,
        which may have been obtained from a DHCP server. */
        FreeRTOS_GetAddressConfiguration( &ulIPAddress,
                                          &ulNetMask,
                                          &ulGatewayAddress,
                                          &ulDNSServerAddress );

        /* Convert the IP address to a string then print it out. */
        FreeRTOS_inet_ntoa( ulIPAddress, ( char * ) cBuffer );
        FreeRTOS_printf(( "IP Address: %s\n", cBuffer ));

        /* Convert the net mask to a string then print it out. */
        FreeRTOS_inet_ntoa( ulNetMask, ( char * ) cBuffer );
        FreeRTOS_printf(( "Subnet Mask: %s\n", cBuffer ));

        /* Convert the IP address of the gateway to a string then print it out. */
        FreeRTOS_inet_ntoa( ulGatewayAddress, ( char * ) cBuffer );
        FreeRTOS_printf(( "Gateway IP Address: %s\n", cBuffer ));

        /* Convert the IP address of the DNS server to a string then print it out. */
        FreeRTOS_inet_ntoa( ulDNSServerAddress, ( char * ) cBuffer );
        FreeRTOS_printf(( "DNS server IP Address: %s\n", cBuffer ));
        vARPSendGratuitous();
    }
}

static void prvEnableEthernetClockDomain( void )
{
    uint32_t ulError;
    uint32_t ulServiceError = 0;
    uint32_t ulCtrl;
    uint32_t ulEna;
    run_profile_t xRunProfile = { 0 };

    se_services_port_init();

    if( board_clocks_config( CLKEN_HFOSC_MASK | CLKEN_CLK_100M_MASK | CLKEN_SRAM0_MASK ) != 0 )
    {
        printf( "board_clocks_config failed\n" );
    }

    ulError = SERVICES_clocks_enable_clock( se_services_s_handle, CLKEN_CLK_50M, true, &ulServiceError );
    if( ulError != 0 )
    {
        printf( "CLKEN_CLK_50M failed\n" );
    }

    ulError = SERVICES_get_run_cfg( se_services_s_handle, &xRunProfile, &ulServiceError );
    if( ulError != 0 )
    {
        printf( "get_run_cfg failed\n" );
        return;
    }

    xRunProfile.power_domains |= PD_SYST_MASK | PD_SRAMS_MASK;
    xRunProfile.memory_blocks |= SRAM0_MASK | MRAM_MASK;
    xRunProfile.ip_clock_gating |= ETH_MASK;
    ulError = SERVICES_set_run_cfg( se_services_s_handle, &xRunProfile, &ulServiceError );
    if( ulError != 0 )
    {
        printf( "set_run_cfg ETH failed\n" );
        return;
    }

    ulCtrl = CLKCTL_PER_MST->ETH_CTRL0;

    /* Power-up ETH: keep isolate+clamp while applying power, then release.
     * PWR_DOWN (bit3)=1 leaves ETH_BASE dead and DMA_BUS_MODE hangs. */
    ulCtrl |= ( 1u << 1 ) | ( 1u << 0 );
    ulCtrl &= ~( 1u << 3 );
    CLKCTL_PER_MST->ETH_CTRL0 = ulCtrl;
    for( ulEna = 0; ulEna < 100000u; ulEna++ )
    {
        __NOP();
    }

    ulCtrl  = CLKCTL_PER_MST->ETH_CTRL0;
    ulCtrl &= ~( ( 1u << 1 ) | ( 1u << 0 ) );
    /* RMII_CLKSEL (bit4): 0 = 50 MHz from the ETH_REFCLK pin, 1 = internal
     * PLL. AppKit selects ETH_REFCLK_B on P11_0 fed from the RTL8201 CLKOUT,
     * and RMSR leaves CLKDIR=0 so the PHY drives that clock. Selecting the
     * PLL put MAC and PHY on two unsynchronised 50 MHz domains: MDIO and
     * link detection still worked (both are independent of REF_CLK) while
     * every MMC packet counter stayed at 0. */
    ulCtrl &= ~( 1u << 4 );
    CLKCTL_PER_MST->ETH_CTRL0 = ulCtrl;

    enable_eth_periph_clk();
    for( ulEna = 0; ulEna < 100000u; ulEna++ )
    {
        __NOP();
    }

    ( void ) CLKCTL_PER_MST->PERIPH_CLK_ENA;
    ( void ) *( ( volatile uint32_t * ) ETH_BASE );
}

void vApplicationStackOverflowHook(TaskHandle_t pxTask, char *pcTaskName)
{
   (void) pxTask;

   SEGGER_RTT_WriteString( 0, "stack overflow: " );
   if( pcTaskName != NULL )
   {
       SEGGER_RTT_WriteString( 0, pcTaskName );
   }
   SEGGER_RTT_WriteString( 0, "\r\n" );

   for (;;);
}

/**
 * @brief The main function
 *
 * Apart from the system/OS initialization, this function calls FreeRTOS_IPInit()
 * to create the FreeRTOS IP task and to initialize the stack. This must be the
 * the first freeRTOS-Plus-TCP function called.
 */
int main (void) {

    // System Initialization
    SystemCoreClockUpdate();

    /* nosys _isatty() fails, so newlib fully-buffers stdout and printf never
     * reaches the RTT _write() hook. Init RTT and force unbuffered output. */
    SEGGER_RTT_Init();
    setvbuf( stdout, NULL, _IONBF, 0 );
    SEGGER_RTT_WriteString( 0, "\r\nFreeRTOS-Plus-TCP ready\r\n" );
    fault_dump_enable( true );

    if( board_pins_config() != 0 )
    {
        printf( "board_pins_config failed\n" );
        for( ;; )
        {
        }
    }

    printf( "FreeRTOS-Plus-TCP demo: static IP %d.%d.%d.%d\n",
            configIP_ADDR0, configIP_ADDR1, configIP_ADDR2, configIP_ADDR3 );

    prvEnableEthernetClockDomain();
    vAppEthPhyHoldOutOfReset();

    /* Start the FreeRTOS IP task */
    FreeRTOS_IPInit(
        ucIPAddress,
        ucNetMask,
        ucGatewayAddress,
        ucDNSServerAddress,
        ucMACAddress );

    /* Start the FreeRTOS Scheduler */
    vTaskStartScheduler();

    /* Should never get here! */
    return 0;
}

/* Newlib stubs. _isatty must return 1 so printf is line-buffered onto RTT. */
int _close( int fd )
{
    ( void ) fd;
    return -1;
}

int _lseek( int fd, int ptr, int dir )
{
    ( void ) fd;
    ( void ) ptr;
    ( void ) dir;
    return 0;
}

int _read( int fd, char * ptr, int len )
{
    ( void ) fd;
    ( void ) ptr;
    ( void ) len;
    return 0;
}

int _fstat( int fd, void * st )
{
    ( void ) fd;
    ( void ) st;
    errno = ENOSYS;
    return -1;
}

int _isatty( int fd )
{
    ( void ) fd;
    return 1;
}

int _getpid( void )
{
    return 1;
}

int _kill( int pid, int sig )
{
    ( void ) pid;
    ( void ) sig;
    errno = ENOSYS;
    return -1;
}
