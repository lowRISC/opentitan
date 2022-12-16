// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_HW_DV_DPI_USBDPI_USBDPI_H_
#define OPENTITAN_HW_DV_DPI_USBDPI_USBDPI_H_

#define TOOL_VERILATOR 1
#define TOOL_INCISIVE 0

#include <assert.h>
#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#if USBDPI_STANDALONE
// For stricter compilation checks, and building faster standalone
typedef uint32_t svBitVecVal;
#else
#include <svdpi.h>
#endif

#include "usb_monitor.h"
#include "usb_transfer.h"

// How many bits in our frame
//
//   (frames on a Full Speed USB link are 1ms, with 12Mbps signalling, but the
//    USB device supports only data transfers of up to 64 bytes, so a 1ms
//    frame interval makes the simulation needlessly long)
#define FRAME_INTERVAL 256 * 8  // 0.17ms, more than enough for our transfers

// How many bits after start to assert VBUS
#define SENSE_AT 20 * 8

// Logging level (parameter to module)
#define LOG_MON 0x01  // USB monitor logging (packet level)
#define LOG_BIT 0x08  // bit level

// Error insertion
#define INSERT_ERR_CRC 0
#define INSERT_ERR_PID 0
#define INSERT_ERR_BITSTUFF 0
#define INSERT_ERR_DATA_TOGGLE 0

// Endpoints used during top-level tests
#define ENDPOINT_ZERO 0         // Endpoint Zero (for the Default Control Pipe)
#define ENDPOINT_SERIAL0 1      // For basic serial communications test
#define ENDPOINT_STREAM_IN 2    // For streaming LFSR data (IN to host)
#define ENDPOINT_SERIAL1 2      // Second serial channel
#define ENDPOINT_ISOCHRONOUS 3  // For basic testing of Isochronous transfers
#define ENDPOINT_STREAM_OUT 4   // For streaming LFSR data (OUT from host)
#define ENDPOINT_UNIMPLEMENTED \
  15  // For testing of response to unimplemented
      // endpoints

#define D2P_BITS 11
#define D2P_DP 1024
#define D2P_DP_EN 512
#define D2P_DN 256
#define D2P_DN_EN 128
#define D2P_D 64
#define D2P_D_EN 32
#define D2P_SE0 16
#define D2P_TX_USE_D_SE0 8
#define D2P_DPPU 4
#define D2P_DNPU 2
#define D2P_RX_ENABLE 1
// Either pullup (dp/dn swapped if the pullup is on DN)
#define D2P_PU (D2P_DPPU | D2P_DNPU)

#define P2D_SENSE 1
#define P2D_DN 2
#define P2D_DP 4
#define P2D_D 8

#define ST_IDLE 0
#define ST_SEND 1
#define ST_GET 2
#define ST_SYNC 3
#define ST_EOP 4
#define ST_EOP0 5

/* Test steps */
// TODO - these are simply bus frame numbers at present, but the DPI
//        shall be changed to respond to the device to avoid assuming the
//        speed/timing of the SW/CPU/USBDEV activity should not be assumed
#define STEP_SET_DEVICE_ADDRESS 1U
#define STEP_READ_DESCRIPTOR 2U
#define STEP_SET_DEVICE_CONFIG 3U
// TODO - these should be advanced once we respond to device
#define STEP_FIRST_READ 9U
#define STEP_READ_BAUD 10U
#define STEP_SECOND_READ 14U
#define STEP_SET_BAUD 15U
#define STEP_THIRD_READ 16U
#define STEP_TEST_ISO1 17U
#define STEP_TEST_ISO2 18U
#define STEP_ENDPT_UNIMPL_SETUP 20U
#define STEP_ENDPT_UNIMPL_OUT 21U
#define STEP_ENDPT_UNIMPL_IN 22U
#define STEP_DEVICE_UK_SETUP 23U
#define STEP_IDLE_START 23U
#define STEP_IDLE_END 33U

/* Remember these go LSB first */

/* Sync is KJKJKJKK */
#define USB_SYNC 0x2a

/* USB Packet IDentifiers */
#define USB_PID_OUT 0xE1U
#define USB_PID_IN 0x69U
#define USB_PID_SOF 0xA5U
#define USB_PID_SETUP 0x2DU
#define USB_PID_DATA0 0xC3U
#define USB_PID_DATA1 0x4BU
#define USB_PID_ACK 0xD2U
#define USB_PID_NAK 0x5AU
#define USB_PID_STALL 0x1EU
#define USB_PID_NYET 0x96U
#define USB_PID_PING 0xB4U

/* USB Standard Request Codes */
#define USB_REQ_GET_STATUS 0x00U
#define USB_REQ_CLEAR_FEATURE 0x01U
#define USB_REQ_SET_FEATURE 0x03U
#define USB_REQ_SET_ADDRESS 0x05U
#define USB_REQ_GET_DESCRIPTOR 0x06U
#define USB_REQ_SET_DESCRIPTOR 0x07U
#define USB_REQ_GET_CONFIGURATION 0x08U
#define USB_REQ_SET_CONFIGURATION 0x09U
#define USB_REQ_GET_INTERFACE 0x0AU
#define USB_REQ_SET_INTERFACE 0x0BU
#define USB_REQ_SYNCH_FRAME 0x0CU

/* Host states */
#define HS_STARTFRAME 0
#define HS_WAITACK 1
#define HS_SET_DATASTAGE 2
#define HS_DS_RXDATA 3
#define HS_DS_SENDACK 4
#define HS_DONEDADR 5
#define HS_REQDATA 6
#define HS_WAITDATA 7
#define HS_SENDACK 8
#define HS_WAIT_PKT 9
#define HS_ACKIFDATA 10
#define HS_SENDHI 11
#define HS_EMPTYDATA 12
#define HS_WAITACK2 13
#define HS_NEXTFRAME 14

// Device address to be used for the USBDEV IP block
#define USBDEV_ADDRESS 2

// Unknown device address (check USBDEV ignores traffic to other devices)
#define UKDEV_ADDRESS 6

// Special value that denotes that this transfer does not include a data stage
#define USBDPI_NO_DATA_STAGE ((uint8_t)~0U)

// Maximum number of simultaneous transfer descriptors
//   (The host model may simply avoid polling for further IN transfers
//    whilst there are no further desciptors available)
#define USBDPI_MAX_TRANSFERS 0x10U

#ifdef __cplusplus
extern "C" {
#endif

// state numbers are annotated purely to add waveform comprehension
typedef enum usbdpi_bus_state {
  kUsbIdle = 0,
  kUsbControlSetup,
  kUsbControlSetupAck,
  kUsbControlDataOut,
  kUsbControlDataOutAck,  // 4
  kUsbControlStatusInToken,
  kUsbControlStatusInData,
  kUsbControlStatusInAck,

  kUsbControlDataInToken,  // 8
  kUsbControlDataInData,
  kUsbControlDataInAck,
  kUsbControlStatusOut,
  kUsbControlStatusOutAck,  // 0xc
  kUsbIsoToken,
  kUsbIsoDataIn,
  kUsbIsoDataOut,

  kUsbBulkOut,  // 0x10
  kUsbBulkOutAck,
  kUsbBulkInToken,
  kUsbBulkInData,
  kUsbBulkInAck,
} usbdpi_bus_state_t;

/**
 * USB DPI state information
 */
struct usbdpi_ctx {
  // Bus signalling state
  usbdpi_bus_state_t bus_state;
  uint32_t driving;
  int linebits;
  int bit;
  int byte;

  /**
   * Next DATAx (DATA0 or DATA1) to be transmitted; advanced when ACKed
   * and reset after SETUP packet transmitted
   */
  uint8_t tx_next_data;
  /**
   * Next DATAx PID (DATA0 or DATA1) expected from device
   */
  uint8_t rx_next_data;

  // Diagnostic logging and bus monitoring
  int loglevel;
  char mon_pathname[FILENAME_MAX];

  /**
   * USB monitor instance
   */
  usb_monitor_ctx_t *mon;

  /**
   * Host controller state
   */
  int hostSt;
  /***
   * Transfer currently being sent to the DUT (NULL iff none)
   */
  usbdpi_transfer_t *sending;

  /***
   * Received transfers
   */
  usbdpi_transfer_t *received;

  // TODO - introduce response detection and retrying
  int retries;

  int last_pu;
  uint8_t lastrxpid;
  int tick;
  int tick_bits;
  int recovery_time;

  /**
   * Test step number
   */
  uint16_t step;

  // Bus framing
  // Note: USB frames are transmitted as 11-bit fields [0,0x7ffU]
  uint16_t frame;
  uint16_t framepend;
  uint16_t lastframe;
  uint16_t inframe;
  int state;
  int wait;

  int baudrate_set_successfully;

  /**
   * Device address currently assigned to the DUT
   */
  uint8_t dev_address;

  /**
   * Linked-list of free transfer descriptors
   */
  usbdpi_transfer_t *free;

  /**
   * Small pool of transfer descriptors
   */
  usbdpi_transfer_t transfer_pool[USBDPI_MAX_TRANSFERS];
};

/**
 * Create a USB DPI instance, returning a 'chandle' for later use
 */
void *usbdpi_create(const char *name, int loglevel);
/**
 * Close a USB DPI instance
 */
void usbdpi_close(void *ctx_void);

/**
 * Respond to device outputs
 */
void usbdpi_device_to_host(void *ctx_void, const svBitVecVal *usb_d2p);

/**
 * Update DPI model outputs
 */
uint8_t usbdpi_host_to_device(void *ctx_void, const svBitVecVal *usb_d2p);

/**
 * Return DPI model diagnostic information for viewing in waveforms
 */
void usbdpi_diags(void *ctx_void, svBitVecVal *diags);

/**
 * Calculate 5-bit CRC used to check token packets
 */
uint32_t CRC5(uint32_t dwInput, int iBitcnt);

/**
 * Calculate 16-bit CRC used to check data fields
 */
uint32_t CRC16(const uint8_t *data, int bytes);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_HW_DV_DPI_USBDPI_USBDPI_H_
