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

// Shall we employ a proper simulation of the frame interval (1ms)?
// TODO - until such time as we can perform multiple control transfers in a
//        single bus frame, this is impractical because the simulation takes too
//        long and is apt to time out
#define FULL_FRAME 0

// How many bits in our frame
//
//   (frames on a Full Speed USB link are 1ms, with 12Mbps signalling, but the
//    USB device supports only data transfers of up to 64 bytes, so a 1ms
//    frame interval makes the simulation needlessly long)
#if FULL_FRAME
#define FRAME_INTERVAL 12000  // 12Mbps, 1ms frame time
#else
#define FRAME_INTERVAL 6000  // 0.5ms
#endif

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
#define ENDPOINT_SERIAL1 2      // Second serial channel
#define ENDPOINT_ISOCHRONOUS 3  // For basic testing of Isochronous transfers
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

/* Remember these go LSB first */

/* Sync is KJKJKJKK */
#define USB_SYNC 0x2AU

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

/* USB Descriptor Types */
#define USB_DESC_TYPE_DEVICE 0x01U
#define USB_DESC_TYPE_CONFIGURATION 0x02U
#define USB_DESC_TYPE_STRING 0x03U
#define USB_DESC_TYPE_INTERFACE 0x04U
#define USB_DESC_TYPE_ENDPOINT 0x05U
#define USB_DESC_TYPE_DEVICE_QUALIFIER 0x06U
#define USB_DESC_TYPE_OTHER_SPEED_CONFIG 0x07U
#define USB_DESC_TYPE_INTERFACE_POWER 0x08U

// Device address to be used for the USBDEV IP block
#define USBDEV_ADDRESS 2

// Unknown device address (check USBDEV ignores traffic to other devices)
#define UKDEV_ADDRESS 6

// Maximum number of endpoints implemented by the USBDEV IP
#define USBDEV_MAX_ENDPOINTS 12U

// Maximum number of endpoints supported by the DPI model
#define USBDPI_MAX_ENDPOINTS 16U

// Maximum number of simultaneous transfer descriptors
//   (The host model may simply avoid polling for further IN transfers
//    whilst there are no further desciptors available)
#define USBDPI_MAX_TRANSFERS 0x10U

// Time intervals for common transactions, in bits
// (allowing for bit stuffing and bus turnaround etc; for setting timeouts)
#define USBDPI_INTERVAL_SETUP_STAGE 200U

// Return the time at which the given number of bit intervals shall have elapsed
#define USBDPI_TIMEOUT(ctx, bits) ((ctx)->tick_bits + (bits))

// Maximum length of test status message
#define USBDPI_MAX_TEST_MSG_LEN 80U

// Vendor-specific commands used for test framework
#define USBDPI_VENDOR_TEST_CONFIG 0x7CU
#define USBDPI_VENDOR_TEST_STATUS 0x7EU

// Next DATAx PID to be used (transmission) or expected (reception)
#define DATA_TOGGLE_ADVANCE(pid) \
  ((pid) == USB_PID_DATA1 ? USB_PID_DATA0 : USB_PID_DATA1)

#ifdef __cplusplus
extern "C" {
#endif

// USBDPI driver states
typedef enum {
  ST_IDLE = 0,
  ST_SEND = 1,
  ST_GET = 2,
  ST_SYNC = 3,
  ST_EOP = 4,
  ST_EOP0 = 5
} usbdpi_drv_state_t;

// Test steps
typedef enum {

  STEP_BUS_RESET = 0u,
  STEP_SET_DEVICE_ADDRESS,
  STEP_GET_DEVICE_DESCRIPTOR,
  STEP_GET_CONFIG_DESCRIPTOR,
  STEP_GET_FULL_CONFIG_DESCRIPTOR,
  STEP_SET_DEVICE_CONFIG,

  // Read test configuration
  // This is a bespoke 'vendor' command via which we inquire of the CPU
  // software what behaviour is required
  STEP_GET_TEST_CONFIG,
  // Report test status (pass/failure) to the CPU software
  STEP_SET_TEST_STATUS,

  // usbdev_test
  STEP_FIRST_READ,
  STEP_READ_BAUD,
  STEP_SECOND_READ,
  STEP_SET_BAUD,
  STEP_THIRD_READ,
  STEP_TEST_ISO1,
  STEP_TEST_ISO2,
  STEP_ENDPT_UNIMPL_SETUP,
  STEP_ENDPT_UNIMPL_OUT,
  STEP_ENDPT_UNIMPL_IN,
  STEP_DEVICE_UK_SETUP,
  STEP_IDLE_START,
  STEP_IDLE_END = STEP_IDLE_START + 4,

  // usbdev_stream_test
  STEP_STREAM_SERVICE = 0x20u,

  // Disconnect the device and stop
  STEP_BUS_DISCONNECT = 0x7fu
} usbdpi_test_step_t;

// Host states
typedef enum {
  HS_STARTFRAME = 0,
  HS_WAITACK = 1,
  HS_SET_DATASTAGE = 2,

  HS_DS_RXDATA = 3,
  HS_DS_SENDACK = 4,
  HS_DONEDADR = 5,
  HS_REQDATA = 6,
  HS_WAITDATA = 7,
  HS_SENDACK = 8,
  HS_WAIT_PKT = 9,
  HS_ACKIFDATA = 10,
  HS_SENDHI = 11,
  HS_EMPTYDATA = 12,
  HS_WAITACK2 = 13,
  HS_STREAMOUT = 14,
  HS_STREAMIN = 15,
  HS_NEXTFRAME = 16
} usbdpi_host_state_t;

typedef enum usbdpi_bus_state {
  kUsbIdle = 0,
  kUsbControlSetup,
  kUsbControlSetupAck,
  kUsbControlDataOut,
  kUsbControlDataOutAck,
  kUsbControlStatusInToken,
  kUsbControlStatusInData,
  kUsbControlStatusInAck,

  kUsbControlDataInToken,
  kUsbControlDataInData,
  kUsbControlDataInAck,
  kUsbControlStatusOut,
  kUsbControlStatusOutAck,
  kUsbIsoToken,
  kUsbIsoDataIn,
  kUsbIsoDataOut,

  kUsbBulkOut,
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
   * Test number, retrieved from the software
   */
  uint16_t test_number;
  /**
   * Test-specific arguments
   */
  uint8_t test_arg[4];
  /**
   * Test status
   * TODO - introduce enum indicating the test status, or borrow from
   *        the existing source tree; we indicate progress too in other places
   */
  uint32_t test_status;
  char test_msg[USBDPI_MAX_TEST_MSG_LEN];

  /**
   * Context for IN endpoints
   */
  struct {
    /**
     * Next DATAx PID (DATA0 or DATA1) expected from device
     */
    uint8_t next_data;
  } ep_in[USBDPI_MAX_ENDPOINTS];
  /**
   * Context for OUT endpoints
   */
  struct {
    /**
     * Next DATAx (DATA0 or DATA1) to be transmitted; advanced when ACKed
     * and reset after SETUP packet transmitted
     */
    uint8_t next_data;
  } ep_out[USBDPI_MAX_ENDPOINTS];

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
  usbdpi_host_state_t hostSt;
  /**
   * Transfer currently being received from the DUT (NULL iff none)
   */
  usbdpi_transfer_t *recving;
  /***
   * Transfer currently being sent to the DUT (NULL iff none)
   */
  usbdpi_transfer_t *sending;

  int last_pu;
  uint8_t lastrxpid;

  /**
   * Count of clock cycles
   */
  uint32_t tick;
  /**
   * Current time in USB bit intervals
   */
  uint32_t tick_bits;

  int recovery_time;

  /**
   * Test step number
   */
  usbdpi_test_step_t step;

  // Bus framing
  // Note: USB frame numbers are transmitted as 11-bit fields [0,0x7ffU]
  uint16_t frame;
  uint16_t framepend;

  /**
   * Time at which the current frame started (bit intervals)
   */
  uint32_t frame_start;

  /**
   * Wait timeout for current operation (bit intervals)
   */
  uint32_t wait;

  /**
   * DPI driver state
   */
  usbdpi_drv_state_t state;

  int baudrate_set_successfully;

  /**
   * Device address currently assigned to the DUT
   */
  uint8_t dev_address;
  /**
   * Length of configuration descriptor
   */
  uint16_t cfg_desc_len;
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
