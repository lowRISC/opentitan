// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "usbdpi.h"

#include <assert.h>
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>

#include "usb_utils.h"
#include "usbdpi_test.h"

// Indexed directly by ctx->state (ST_)
static const char *st_states[] = {"ST_IDLE 0", "ST_SEND 1", "ST_GET 2",
                                  "ST_SYNC 3", "ST_EOP 4",  "ST_EOP0 5"};

// Indexed directly by ct-x>hostSt (HS_)
static const char *hs_states[] = {
    "HS_STARTFRAME 0", "HS_WAITACK 1",   "HS_SET_DATASTAGE 2", "HS_DS_RXDATA 3",
    "HS_DS_SENDACK 4", "HS_DONEDADR 5",  "HS_REQDATA 6",       "HS_WAITDATA 7",
    "HS_SENDACK 8",    "HS_WAIT_PKT 9",  "HS_ACKIFDATA 10",    "HS_SENDHI 11",
    "HS_EMPTYDATA 12", "HS_WAITACK2 13", "HS_STREAMOUT 14",    "HS_STREAMIN 15",
    "HS_NEXTFRAME 16", "HS_ERROR 17"};

static const char *decode_usb[] = {"SE0", "0-K", "1-J", "SE1"};

// Optionally invert the signals the host is driving, according to bus
// configuration
static uint32_t inv_driving(usbdpi_ctx_t *ctx, uint32_t d2p);

// Request IN transfer. Get back NAK or DATA0/DATA1.
static void pollRX(usbdpi_ctx_t *ctx, uint8_t endpoint, bool send_hi,
                   bool nak_data);
// Get Baud (Vendor-specific)
static void readBaud(usbdpi_ctx_t *ctx, uint8_t endpoint);

// Get Test Configuration (Vendor-specific)
static void getTestConfig(usbdpi_ctx_t *ctx, uint16_t desc_len);

// Get Descriptor
static void getDescriptor(usbdpi_ctx_t *ctx, uint8_t desc_type,
                          uint8_t desc_idx, uint16_t desc_len);
// Set Baud (Vendor-specific)
static void setBaud(usbdpi_ctx_t *ctx, uint8_t endpoint);

// Set device address (with null data stage)
static void setDeviceAddress(usbdpi_ctx_t *ctx, uint8_t dev_addr);

// Set device configuration
static void setDeviceConfiguration(usbdpi_ctx_t *ctx, uint8_t config);

// Set test status, reporting progress/success/failure (Vendor-specific)
static void setTestStatus(usbdpi_ctx_t *ctx, uint32_t status, const char *msg);

// Change DP and DN outputs from host
static uint32_t set_driving(usbdpi_ctx_t *ctx, uint32_t d2p, uint32_t newval,
                            bool p2d_oe);

// Try to send OUT transfer. Optionally expect Status packet (eg. ACK|NAK) in
// response
static void tryTX(usbdpi_ctx_t *ctx, uint8_t endpoint, bool expect_status);

// Test the ischronous transfers (without ACKs)
// static void testIso(usbdpi_ctx_t *ctx);
#define testIso(ctx) tryTX((ctx), ENDPOINT_ISOCHRONOUS, false)

// Initialize the state of the DPI model appropriately for when the device
// connects to the bus
static void bus_reset(usbdpi_ctx_t *ctx) {
  // Initialize state for each endpoint and direction
  for (unsigned ep = 0U; ep < USBDPI_MAX_ENDPOINTS; ep++) {
    // First DATAx received shall be DATA0
    ctx->ep_in[ep].next_data = USB_PID_DATA0;

    // First DATAx transmitted shall be DATA0 because it must follow a SETUP
    // transaction
    ctx->ep_out[ep].next_data = USB_PID_DATA0;
  }

  ctx->baudrate_set_successfully = 0;
  ctx->state = ST_IDLE;

  ctx->step = STEP_BUS_RESET;
  ctx->hostSt = HS_NEXTFRAME;

  // Device address should be discarded by usbdev, and it should now respond
  // at the default address of 0.
  ctx->dev_address = 0U;
  ctx->bus_state = kUsbIdle;
}

// Callback for USB data detection
static void usbdpi_data_callback(void *ctx_v, usbmon_data_type_t type,
                                 uint8_t d);

/**
 * Create a USB DPI instance, returning a 'chandle' for later use
 */
void *usbdpi_create(const char *name, int loglevel) {
  // Use calloc for zero-initialisation
  usbdpi_ctx_t *ctx = (usbdpi_ctx_t *)calloc(1, sizeof(usbdpi_ctx_t));
  assert(ctx);

  // Note: calloc has initialized most of the fields for us
  // ctx->tick = 0;
  // ctx->tick_bits = 0;
  // ctx->frame = 0;
  // ctx->framepend = false;
  // ctx->frame_start = 0;
  // ctx->last_pu = 0;
  // ctx->driving = 0;

  bus_reset(ctx);

  ctx->loglevel = loglevel;

  char cwd[FILENAME_MAX];
  char *cwd_rv;
  cwd_rv = getcwd(cwd, sizeof(cwd));
  assert(cwd_rv != NULL);

  // Monitor log file
  int rv = snprintf(ctx->mon_pathname, FILENAME_MAX, "%s/%s.log", cwd, name);
  assert(rv <= FILENAME_MAX && rv > 0);

  ctx->mon = usb_monitor_init(ctx->mon_pathname, usbdpi_data_callback, ctx);

  // Prepare the transfer descriptors for use
  usb_transfer_setup(ctx);

  return (void *)ctx;
}

void usbdpi_device_to_host(void *ctx_void, const svBitVecVal *usb_d2p) {
  usbdpi_ctx_t *ctx = (usbdpi_ctx_t *)ctx_void;
  assert(ctx);

  // Ascertain the state of the D+/D- signals from the device
  // TODO - migrate to a simple function
  uint32_t d2p = usb_d2p[0];
  unsigned dp, dn;
  if (d2p & D2P_TX_USE_D_SE0) {
    // Single-ended mode uses D and SE0
    if (d2p & D2P_D_EN) {
      if (d2p & D2P_DNPU) {
        // Pullup says swap i.e. D is inverted
        dp = (d2p & D2P_SE0) ? 0 : ((d2p & D2P_D) ? 0 : 1);
        dn = (d2p & D2P_SE0) ? 0 : ((d2p & D2P_D) ? 1 : 0);
      } else {
        dp = (d2p & D2P_SE0) ? 0 : ((d2p & D2P_D) ? 1 : 0);
        dn = (d2p & D2P_SE0) ? 0 : ((d2p & D2P_D) ? 0 : 1);
      }
    } else {
      dp = (d2p & D2P_PU) ? 1 : 0;
      dn = 0;
    }
  } else {
    // Normal D+/D- mode
    if (d2p & D2P_DNPU) {
      // Assertion of DN pullup suggests DP and DN are swapped
      dp = ((d2p & D2P_DN_EN) && (d2p & D2P_DN)) ||
           (!(d2p & D2P_DN_EN) && (d2p & D2P_DNPU));
      dn = (d2p & D2P_DP_EN) && (d2p & D2P_DP);
    } else {
      // No DN pullup so normal orientation
      dp = ((d2p & D2P_DP_EN) && (d2p & D2P_DP)) ||
           (!(d2p & D2P_DP_EN) && (d2p & D2P_DPPU));
      dn = (d2p & D2P_DN_EN) && (d2p & D2P_DN);
    }
  }

  // TODO - check the timing of the device responses to ensure compliance with
  // the specification; the response time of acknowledgements, for example, has
  // a hard real time requirement that is specified in terms of bit intervals
  if (d2p & (D2P_DP_EN | D2P_DN_EN | D2P_D_EN)) {
    switch (ctx->state) {
      // Host to device transmission
      case ST_SYNC:
      case ST_SEND:
      case ST_EOP:
      case ST_EOP0:
        printf(
            "[usbdpi] frame 0x%x tick_bits 0x%x error state %s hs %s and "
            "device "
            "drives 0x%x\n",
            ctx->frame, ctx->tick_bits, st_states[ctx->state],
            hs_states[ctx->hostSt], d2p);
        // TODO: stop the test
        break;

      // Device to host transmission; collect the bits
      case ST_GET:
        // TODO: perform bit-level decoding and packet construction here rather
        // than relying upon usb_monitor to do that
        // TODO: synchronize with the device transmission and check that the
        // signals remain stable across all 4 cycles of the bit interval
        break;

      case ST_IDLE:
        // Device is trying to transmit and we're not transmitting, so switch to
        // receiving a packet.
        ctx->state = ST_GET;
        break;

      default:
        assert(!"Invalid/unknown state");
        break;
    }
  } else {
    if (ctx->state == ST_GET) {
      ctx->state = ST_IDLE;
    }
  }

  if ((d2p & D2P_DNPU) && (d2p & D2P_DPPU)) {
    printf("[usbdpi] frame 0x%x tick_bits 0x%x error both pullups are driven\n",
           ctx->frame, ctx->tick_bits);
  }
  if ((d2p & D2P_PU) != ctx->last_pu) {
    usb_monitor_log(ctx->mon, "0x%-3x 0x%-8x Pullup change to %s%s%s\n",
                    ctx->frame, ctx->tick_bits,
                    (d2p & D2P_DPPU) ? "DP Pulled up " : "",
                    (d2p & D2P_DNPU) ? "DN Pulled up " : "",
                    (d2p & D2P_TX_USE_D_SE0) ? "SingleEnded" : "Differential");

    ctx->last_pu = d2p & D2P_PU;
  }

  // TODO - prime candidate for a function
  if (ctx->loglevel & LOG_BIT) {
    char raw_str[D2P_BITS + 1];
    {
      int i;
      for (i = 0; i < D2P_BITS; i++) {
        raw_str[D2P_BITS - i - 1] = d2p & (1 << i) ? '1' : '0';
      }
    }
    raw_str[D2P_BITS] = 0;

    const char *pullup = (d2p & D2P_PU) ? "PU" : "  ";
    const char *state =
        (ctx->state == ST_GET) ? decode_usb[dp << 1 | dn] : "ZZ ";
    usb_monitor_log(ctx->mon, "0x%-3x 0x%-8x %s %s %s %x\n", ctx->frame,
                    ctx->tick_bits, raw_str, pullup, state, d2p);
  }

  // Device-to-Host EOP
  if (ctx->state == ST_GET && dp == 0 && dn == 0) {
    switch (ctx->bus_state) {
      // Control Transfers
      case kUsbControlSetup:
        ctx->bus_state = kUsbControlSetupAck;
        break;
      case kUsbControlDataOut:
        ctx->bus_state = kUsbControlDataOutAck;
        break;
      case kUsbControlStatusInToken:
        ctx->bus_state = kUsbControlStatusInData;
        break;
      case kUsbControlDataInToken:
        ctx->bus_state = kUsbControlDataInData;
        break;
      case kUsbControlStatusOut:
        ctx->bus_state = kUsbControlStatusOutAck;
        break;

      // Isochronous Transfers
      case kUsbIsoInToken:
        ctx->bus_state = kUsbIsoInData;
        break;

      // Bulk Transfers
      case kUsbBulkOut:
        ctx->bus_state = kUsbBulkOutAck;
        break;
      case kUsbBulkInToken:
        ctx->bus_state = kUsbBulkInData;
        break;

      // Interrupt Transfers
      case kUsbInterruptOut:
        ctx->bus_state = kUsbInterruptOutAck;
        break;
      case kUsbInterruptInToken:
        ctx->bus_state = kUsbInterruptInData;
        break;

      // TODO - this shall become an error condition; we're not expecting
      //        a transmission from the device, and thus no EOP either
      default:
        break;
    }
  }
}

// Callback for USB data detection
// - the DPI host model presently does not duplicate the bit-level decoding and
//   packet construction of the usb_monitor, so we piggyback on its decoding and
//   trust it to be neutral.
//
// Note: this is invoked for any byte transferred over the USB; both
// host-to-device and device-to-host traffic
void usbdpi_data_callback(void *ctx_v, usbmon_data_type_t type, uint8_t d) {
  usbdpi_ctx_t *ctx = (usbdpi_ctx_t *)ctx_v;
  assert(ctx);

  // We are interested only in the packets from device to host
  if (ctx->state != ST_GET) {
    return;
  }

  // Ensure that we have a buffer available for packet reception
  if (!ctx->recving) {
    ctx->recving = transfer_alloc(ctx);
  }

  usbdpi_transfer_t *tr = ctx->recving;
  // TODO - commute to run time error indicating buffer exhaustion
  assert(tr);
  if (tr) {
    if (false) {  // ctx->loglevel & LOG_MON) {
      printf("[usbdpi] data type %u d 0x%02x\n", type, d);
    }

    bool ok = false;
    switch (type) {
      case UsbMon_DataType_Sync:
        // Initialize/rewind the received transfer
        transfer_init(tr);
        ok = true;
        break;
      case UsbMon_DataType_EOP:
        ok = true;
        break;
      // Collect the PID and any subsequent data bytes
      case UsbMon_DataType_PID:
        switch (d) {
          case USB_PID_DATA0:
          case USB_PID_DATA1: {
            // TODO - this records the start of the data field with the
            // current transfer descriptors
            uint8_t *dp = transfer_data_start(tr, d, 0U);
            ok = (dp != NULL);
          } break;
          default:
            ok = transfer_append(tr, &d, 1);
            break;
        }
        break;
      // Collect data field
      case UsbMon_DataType_Byte:
        ok = transfer_append(tr, &d, 1);
        break;
      default:
        assert(!"Unknown/unhandled rx type from monitor");
        break;
    }

    // TODO - commute to run time error indicating excessive packet length
    assert(ok);
  }
}

// Set device address (with null data stage)
void setDeviceAddress(usbdpi_ctx_t *ctx, uint8_t dev_addr) {
  usbdpi_transfer_t *tr = ctx->sending;
  uint8_t *dp;
  switch (ctx->hostSt) {
    case HS_STARTFRAME:
      // Setting device address
      //   (uses address 0 initially, so if this SETUP message is intended to
      //    be received, `dev_address` should be zero at this point.)
      transfer_token(tr, USB_PID_SETUP, ctx->dev_address, ENDPOINT_ZERO);

      dp = transfer_data_start(tr, USB_PID_DATA0, 8);
      if (INSERT_ERR_PID) {
        *(dp - 1) = 0xc4U;
      }
      dp[0] = 0;  // h2d, std, device
      dp[1] = USB_REQ_SET_ADDRESS;
      dp[2] = dev_addr;  // device address
      dp[3] = 0;
      // Trigger bitstuffing, technically the device
      // behavior is unspecified with wIndex != 0
      dp[4] = 0xFF;  // wIndex = 0xFF00
      dp[5] = 0;
      dp[6] = 0;  // wLength = 0
      dp[7] = 0;
      transfer_data_end(tr, dp + 8);
      if (INSERT_ERR_CRC) {
        // Flip the last CRC bit to emulate a CRC error
        dp[9] ^= 0x01u;
      }
      transfer_send(ctx, tr);
      ctx->bus_state = kUsbControlSetup;
      ctx->hostSt = HS_WAITACK;
      break;
    case HS_WAITACK:
      ctx->wait = ctx->tick_bits + 532;  // HACK
      ctx->hostSt = HS_SET_DATASTAGE;
      break;
    case HS_SET_DATASTAGE:
      if (ctx->bus_state == kUsbControlSetupAck &&
          ctx->tick_bits >= ctx->wait) {
        transfer_token(tr, USB_PID_IN, 0, 0);
        transfer_send(ctx, tr);
        ctx->bus_state = kUsbControlStatusInToken;
        ctx->hostSt = HS_DS_RXDATA;
      }
      break;
    case HS_DS_RXDATA:
      ctx->wait = ctx->tick_bits + 24;  // HACK -- 2 bytes
      ctx->hostSt = HS_DS_SENDACK;
      break;
    case HS_DS_SENDACK:
      if (ctx->bus_state == kUsbControlStatusInData ||
          ctx->tick_bits >= ctx->wait) {
        transfer_status(ctx, tr, USB_PID_ACK);
        ctx->bus_state = kUsbIdle;
        ctx->hostSt = HS_NEXTFRAME;

        // Remember the assigned device address
        ctx->dev_address = dev_addr;

        printf("[usbdpi] setDeviceAddress done\n");
      }
      break;
    default:
      break;
  }
}

// Set device configuration
void setDeviceConfiguration(usbdpi_ctx_t *ctx, uint8_t config) {
  usbdpi_transfer_t *tr = ctx->sending;
  uint8_t *dp;
  switch (ctx->hostSt) {
    case HS_STARTFRAME:
      transfer_token(tr, USB_PID_SETUP, ctx->dev_address, ENDPOINT_ZERO);

      dp = transfer_data_start(tr, USB_PID_DATA0, 8);
      dp[0] = 0;  // h2d, std, device
      dp[1] = USB_REQ_SET_CONFIGURATION;
      dp[2] = config;
      dp[3] = 0;
      dp[4] = 0;  // wIndex = 0
      dp[5] = 0;
      dp[6] = 0;  // wLength = 0
      dp[7] = 0;
      transfer_data_end(tr, dp + 8);

      transfer_send(ctx, tr);
      ctx->bus_state = kUsbControlSetup;
      ctx->hostSt = HS_WAITACK;
      break;
    case HS_WAITACK:
      ctx->wait = ctx->tick_bits + 532;  // HACK
      ctx->hostSt = HS_SET_DATASTAGE;
      break;
    case HS_SET_DATASTAGE:
      if (ctx->bus_state == kUsbControlSetupAck &&
          ctx->tick_bits >= ctx->wait) {
        transfer_token(tr, USB_PID_IN, ctx->dev_address, ENDPOINT_ZERO);
        transfer_send(ctx, tr);
        ctx->bus_state = kUsbControlStatusInToken;
        ctx->hostSt = HS_DS_RXDATA;
      }
      break;
    case HS_DS_RXDATA:
      ctx->wait = ctx->tick_bits + 24;  // HACK -- 2 bytes
      ctx->hostSt = HS_DS_SENDACK;
      break;
    case HS_DS_SENDACK:
      if (ctx->bus_state == kUsbControlStatusInData ||
          ctx->tick_bits >= ctx->wait) {
        transfer_status(ctx, tr, USB_PID_ACK);
        ctx->bus_state = kUsbIdle;
        ctx->hostSt = HS_NEXTFRAME;
        printf("[usbdpi] setDeviceConfiguration done\n");
      }
      break;
    default:
      break;
  }
}

// Get Descriptor
void getDescriptor(usbdpi_ctx_t *ctx, uint8_t desc_type, uint8_t desc_idx,
                   uint16_t desc_len) {
  usbdpi_transfer_t *tr = ctx->sending;
  uint8_t *dp;
  switch (ctx->hostSt) {
    case HS_STARTFRAME: {
      // TODO - build the bmRequestType by ORing values
      const uint8_t bmRequestType = 0x80;  // d2h, vendor, endpoint
      uint16_t wValue = (desc_type << 8) | (uint8_t)desc_idx;
      transfer_setup(ctx, tr, bmRequestType, USB_REQ_GET_DESCRIPTOR, wValue, 0U,
                     desc_len);
    } break;
    case HS_WAITACK:
      ctx->wait = ctx->tick_bits + 1164;  // HACK
      ctx->hostSt = HS_REQDATA;
      break;
    case HS_REQDATA:
      // TODO - we must wait before trying the IN because we currently
      // do not retry after a NAK response, but the CPU software can be tardy
      if (ctx->tick_bits >= ctx->wait &&
          ctx->bus_state == kUsbControlSetupAck) {
        transfer_token(tr, USB_PID_IN, ctx->dev_address, ENDPOINT_ZERO);

        transfer_send(ctx, tr);
        ctx->bus_state = kUsbControlDataInToken;
        ctx->hostSt = HS_WAITDATA;
      }
      break;
    case HS_WAITDATA:
      ctx->wait = ctx->tick_bits + 2000;  // HACK
      ctx->hostSt = HS_SENDACK;
      break;
    case HS_SENDACK:
      if (ctx->bus_state == kUsbControlDataInData) {
        if (ctx->step == STEP_GET_CONFIG_DESCRIPTOR) {
          // Check the GET_DESCRIPTOR response
          assert(ctx->recving);

          // TODO - detect when the returned data falls short of the requested
          // transfer length
          uint8_t *dp = transfer_data_field(ctx->recving);
          assert(dp);
          // Collect the returned values
          // uint8_t  bLength = dp[0];
          // uint8_t  bDescriptorType = dp[1];
          uint16_t wTotalLength = dp[2] | (dp[3] << 8);
          // uint8_t  bNumInterfaces = dp[4];

          ctx->cfg_desc_len = wTotalLength;
        }

        transfer_token(tr, USB_PID_ACK, ctx->dev_address, ENDPOINT_ZERO);

        transfer_send(ctx, tr);
        ctx->bus_state = kUsbControlDataInAck;
        ctx->hostSt = HS_WAIT_PKT;

        ctx->wait = ctx->tick_bits + 200;  // HACK
      } else if (ctx->tick_bits >= ctx->wait) {
        printf("[usbdpi] Timed out waiting for device\n");
        ctx->hostSt = HS_NEXTFRAME;
        ctx->bus_state = kUsbIdle;
      }
      break;
    case HS_WAIT_PKT:
      // TODO - introduce support for multiple packets when we've requested
      // longer transfers
      if (ctx->tick_bits >= ctx->wait) {
        ctx->hostSt = HS_EMPTYDATA;
      }
      break;
    case HS_EMPTYDATA:
      // Status stage of Control Read
      // Transmit zero-length data packet and await handshake
      transfer_token(tr, USB_PID_OUT, ctx->dev_address, ENDPOINT_ZERO);

      dp = transfer_data_start(tr, USB_PID_DATA1, 0);
      transfer_data_end(tr, dp);
      transfer_send(ctx, tr);
      ctx->bus_state = kUsbControlStatusOut;
      ctx->hostSt = HS_WAITACK2;
      ctx->wait = ctx->tick_bits + 200;  // HACK
      break;
    case HS_WAITACK2:
      if (ctx->bus_state == kUsbControlStatusOutAck) {
        switch (ctx->lastrxpid) {
          case USB_PID_ACK:
            ctx->ep_out[ENDPOINT_ZERO].next_data =
                DATA_TOGGLE_ADVANCE(ctx->ep_out[ENDPOINT_ZERO].next_data);
            ctx->hostSt = HS_NEXTFRAME;
            printf("[usbdpi] getDescriptor done\n");
            break;

          case USB_PID_NAK:
            // TODO - this means that the device is still busy
            ctx->hostSt = HS_WAITACK2;
            ctx->wait = ctx->tick_bits + 200;  // HACK
            break;

          // For DEVICE_QUALIFIER reads we expect a STALL response, being
          // a Full Speed-only device
          // TODO: commute these other responses into test failures
          case USB_PID_STALL:
            printf("[usbdpi] Device stalled\n");
            ctx->hostSt = HS_NEXTFRAME;
            break;
          default:
            printf("[usbdpi] Unexpected handshake response 0x%02x\n",
                   ctx->lastrxpid);
            ctx->hostSt = HS_NEXTFRAME;
            break;
        }
      } else if (ctx->tick_bits >= ctx->wait) {
        printf(
            "[usbdpi] Timed out waiting for device response in Status Stage\n");
        ctx->hostSt = HS_NEXTFRAME;
      }
      break;
    default:
      break;
  }
}

// Get Test Configuration (Vendor-specific)
void getTestConfig(usbdpi_ctx_t *ctx, uint16_t desc_len) {
  usbdpi_transfer_t *tr = ctx->sending;
  uint8_t *dp;
  assert(tr);
  switch (ctx->hostSt) {
    case HS_STARTFRAME: {
      const uint8_t bmRequestType = 0xc2;  // d2h, vendor, endpoint
      transfer_setup(ctx, tr, bmRequestType, USBDPI_VENDOR_TEST_CONFIG, 0U, 0U,
                     desc_len);
    } break;
    case HS_WAITACK:
      ctx->wait = ctx->tick_bits + 1164;  // HACK
      ctx->hostSt = HS_REQDATA;
      break;
    case HS_REQDATA:
      // TODO: we must wait before trying the IN because we currently
      // do not retry after a NAK response, but the CPU software can be tardy
      if (ctx->tick_bits >= ctx->wait &&
          ctx->bus_state == kUsbControlSetupAck) {
        transfer_token(tr, USB_PID_IN, ctx->dev_address, ENDPOINT_ZERO);

        transfer_send(ctx, tr);
        ctx->bus_state = kUsbControlDataInToken;
        ctx->hostSt = HS_WAITDATA;
      }
      break;
    case HS_WAITDATA:
      ctx->wait = ctx->tick_bits + 2000;  // HACK
      ctx->hostSt = HS_SENDACK;
      break;
    case HS_SENDACK:
      if (ctx->bus_state == kUsbControlDataInData) {
        switch (ctx->lastrxpid) {
          case USB_PID_DATA1: {
            usbdpi_transfer_t *rx = ctx->recving;
            assert(rx);
            // TODO: check the length of the received data field!
            uint8_t *dp = transfer_data_field(rx);
            assert(dp);
            // Validate the first part of the test descriptor
            printf("[usbdpi] Test descriptor 0x%.8X\n", get_le32(dp));
            // Check the header signature
            const uint8_t test_sig_head[] = {0x7eu, 0x57u, 0xc0u, 0xf1u};
            const uint8_t test_sig_tail[] = {0x1fu, 0x0cu, 0x75u, 0xe7u};
            if (!memcmp(dp, test_sig_head, 4) && 0x10 == get_le16(&dp[4]) &&
                !memcmp(&dp[12], test_sig_tail, 4)) {
              ctx->test_number = (usb_testutils_test_number_t)get_le16(&dp[6]);
              ctx->test_arg[0] = dp[8];
              ctx->test_arg[1] = dp[9];
              ctx->test_arg[2] = dp[10];
              ctx->test_arg[3] = dp[11];

              printf("[usbdpi] Test number 0x%04x args %02x %02x %02x %02x\n",
                     ctx->test_number, ctx->test_arg[0], ctx->test_arg[1],
                     ctx->test_arg[2], ctx->test_arg[3]);

              usbdpi_test_init(ctx);
            } else {
              printf(
                  "[usbdpi] Invalid/unrecognised test descriptor received\n");
              assert(!"Cannot proceed without test descriptor");
            }
          } break;

          case USB_PID_NAK:
            // TODO: we should retry the request in this case
            printf("[usbdpi] Unable to retrieve test config\n");
            assert(!"DPI is unable to retrieve test config");
            ctx->hostSt = HS_NEXTFRAME;
            break;

          case USB_PID_STALL:
            printf("[usbdpi] Device stalled\n");
            assert(!"Device is stalled");
            ctx->hostSt = HS_NEXTFRAME;
            break;
          default:
            printf("[usbdpi] Unexpected handshake response 0x%02x\n",
                   ctx->lastrxpid);
            assert(!"Unexpected handshake response");
            ctx->hostSt = HS_NEXTFRAME;
            break;
        }
        transfer_token(tr, USB_PID_ACK, ctx->dev_address, ENDPOINT_ZERO);

        transfer_send(ctx, tr);
        ctx->bus_state = kUsbControlDataInAck;
        ctx->hostSt = HS_WAIT_PKT;

        ctx->wait = ctx->tick_bits + 200;  // HACK
      } else if (ctx->tick_bits >= ctx->wait) {
        printf("[usbdpi] Timed out waiting for device\n");
        ctx->hostSt = HS_NEXTFRAME;
        ctx->bus_state = kUsbIdle;
      }
      break;
    case HS_WAIT_PKT:
      if (ctx->tick_bits >= ctx->wait) {
        ctx->hostSt = HS_EMPTYDATA;
      }
      break;
    case HS_EMPTYDATA:
      // Status stage of Control Read
      // Transmit zero-length data packet and await handshake
      transfer_token(tr, USB_PID_OUT, ctx->dev_address, ENDPOINT_ZERO);

      dp = transfer_data_start(tr, USB_PID_DATA1, 0);
      transfer_data_end(tr, dp);
      transfer_send(ctx, tr);
      ctx->bus_state = kUsbControlStatusOut;
      ctx->hostSt = HS_WAITACK2;
      ctx->wait = ctx->tick_bits + 200;  // HACK
      break;
    case HS_WAITACK2:
      if (ctx->bus_state == kUsbControlStatusOutAck) {
        switch (ctx->lastrxpid) {
          case USB_PID_ACK:
            ctx->ep_out[ENDPOINT_ZERO].next_data =
                DATA_TOGGLE_ADVANCE(ctx->ep_out[ENDPOINT_ZERO].next_data);
            ctx->hostSt = HS_NEXTFRAME;
            break;

          case USB_PID_NAK:
            // TODO - this means that the device is still busy
            ctx->hostSt = HS_WAITACK2;
            ctx->wait = ctx->tick_bits + 200;  // HACK
            break;

          // TODO - commute these other responses into test failures
          case USB_PID_STALL:
            printf("[usbdpi] Device stalled\n");
            ctx->hostSt = HS_NEXTFRAME;
            break;
          default:
            printf("[usbdpi] Unexpected handshake response 0x%02x\n",
                   ctx->lastrxpid);
            ctx->hostSt = HS_NEXTFRAME;
            break;
        }
      } else if (ctx->tick_bits >= ctx->wait) {
        printf(
            "[usbdpi] Time out waiting for device response in Status Stage\n");
        ctx->hostSt = HS_NEXTFRAME;
      }
      break;
    default:
      break;
  }
}

// Set Test Status, reporting progress/success/failure (Vendor-specific)
void setTestStatus(usbdpi_ctx_t *ctx, uint32_t status, const char *msg) {
  // TODO - placeholder for reporting of test status reporting and termination
}

// Get Baud (Vendor-specific)
void readBaud(usbdpi_ctx_t *ctx, uint8_t endpoint) {
  usbdpi_transfer_t *tr = ctx->sending;
  uint8_t *dp;
  switch (ctx->hostSt) {
    case HS_STARTFRAME:
      transfer_token(tr, USB_PID_SETUP, ctx->dev_address, endpoint);

      dp = transfer_data_start(tr, USB_PID_DATA0, 0);
      dp[0] = 0xc2;  // d2h, vendor, endpoint
      dp[1] = 2;     // get baud
      dp[2] = 0;     // index 0
      dp[3] = 0;     // type device
      dp[4] = 0;     // wIndex = 0
      dp[5] = 0;
      dp[6] = 0x2;  // wLength = 2
      dp[7] = 0;
      transfer_data_end(tr, dp + 8);

      transfer_send(ctx, tr);
      ctx->bus_state = kUsbControlSetup;
      ctx->hostSt = HS_WAITACK;
      break;
    case HS_WAITACK:
      ctx->wait = ctx->tick_bits + 32;  // HACK
      ctx->hostSt = HS_REQDATA;
      break;
    case HS_REQDATA:
      if (ctx->tick_bits >= ctx->wait) {
        // NOTE: This IN request produces a NAK from the device because there is
        //       nothing available, at which point a REAL host should surely
        //       retry the request at a later time!
        transfer_token(tr, USB_PID_IN, ctx->dev_address, endpoint);

        transfer_send(ctx, tr);
        ctx->hostSt = HS_WAITDATA;
      }
      break;
    case HS_WAITDATA:
      ctx->wait = ctx->tick_bits + 200;  // HACK
      ctx->hostSt = HS_SENDACK;
      break;
    case HS_SENDACK:
      // TODO - are we not ACKing the NAK at this point?
      if (ctx->tick_bits >= ctx->wait) {
        transfer_status(ctx, tr, USB_PID_ACK);
        ctx->hostSt = HS_EMPTYDATA;
      }
      break;
    case HS_EMPTYDATA:
      // Transmit OUT transaction with zero-length DATA packet
      transfer_token(tr, USB_PID_OUT, ctx->dev_address, endpoint);
      if (INSERT_ERR_DATA_TOGGLE) {
        // NOTE: This raises a LinkOutErr on the USBDEV because it is expecting
        //       DATA0
        uint8_t bad_pid = DATA_TOGGLE_ADVANCE(ctx->ep_out[endpoint].next_data);
        dp = transfer_data_start(tr, bad_pid, 0);
      } else {
        dp = transfer_data_start(tr, ctx->ep_out[endpoint].next_data, 0);
      }
      transfer_data_end(tr, dp);

      transfer_send(ctx, tr);
      ctx->bus_state = kUsbControlStatusOut;
      ctx->hostSt = HS_WAITACK2;

      ctx->wait = ctx->tick_bits + 200;  // HACK
      break;
    case HS_WAITACK2:
      if (ctx->tick_bits >= ctx->wait ||
          ctx->bus_state == kUsbControlStatusOutAck) {
        if (ctx->lastrxpid == USB_PID_ACK) {
          ctx->ep_out[endpoint].next_data =
              DATA_TOGGLE_ADVANCE(ctx->ep_out[endpoint].next_data);
        }
        ctx->hostSt = HS_NEXTFRAME;
        printf("[usbdpi] readBaud done\n");
      }
      break;
    default:
      break;
  }
}

// Set Baud (Vendor-specific)
void setBaud(usbdpi_ctx_t *ctx, uint8_t endpoint) {
  usbdpi_transfer_t *tr = ctx->sending;
  uint8_t *dp;
  switch (ctx->hostSt) {
    case HS_STARTFRAME:
      transfer_token(tr, USB_PID_SETUP, ctx->dev_address, endpoint);

      dp = transfer_data_start(tr, USB_PID_DATA0, 0);
      dp[0] = 0x42;  // h2d, vendor, endpoint
      dp[1] = 3;     // set baud
      dp[2] = 96;    // index 0
      dp[3] = 0;     // type device
      dp[4] = 0;     // wIndex = 0
      dp[5] = 0;
      dp[6] = 0;  // wLength = 0
      dp[7] = 0;
      transfer_data_end(tr, dp + 8);

      transfer_send(ctx, tr);
      ctx->bus_state = kUsbControlSetup;
      ctx->hostSt = HS_WAITACK;
      break;
    case HS_WAITACK:
      ctx->wait = ctx->tick_bits + 32;  // HACK
      ctx->hostSt = HS_REQDATA;
      break;
    case HS_REQDATA:
      if (ctx->tick_bits >= ctx->wait) {
        transfer_token(tr, USB_PID_IN, ctx->dev_address, endpoint);

        transfer_send(ctx, tr);
        ctx->hostSt = HS_WAITDATA;
      }
      break;
    case HS_WAITDATA:
      ctx->wait = ctx->tick_bits + 40;  // HACK
      ctx->hostSt = HS_SENDACK;
      break;
    case HS_SENDACK:
      if (ctx->tick_bits >= ctx->wait) {
        transfer_status(ctx, tr, USB_PID_ACK);
        ctx->hostSt = HS_NEXTFRAME;
        ctx->baudrate_set_successfully = 1;
        printf("[usbdpi] setBaud done\n");
      }
      break;
    default:
      break;
  }
}

// Try an OUT transfer to the device, optionally expecting a Status
//   packet (eg. ACK|NAK) in response; this is not expected for
//   Isochronous transfers
void tryTX(usbdpi_ctx_t *ctx, uint8_t endpoint, bool expect_status) {
  const uint8_t pattern[] = {
      "AbCdEfGhIjKlMnOpQrStUvWxYz+0123456789-aBcDeFgHiJkLmNoPqRsTuVwXyZ"};
  usbdpi_transfer_t *tr = ctx->sending;
  uint8_t *dp;
  switch (ctx->hostSt) {
    case HS_STARTFRAME:
      transfer_token(tr, USB_PID_OUT, ctx->dev_address, endpoint);

      dp = transfer_data_start(tr, ctx->ep_out[endpoint].next_data, 0);
      memcpy(dp, pattern, sizeof(pattern));
      transfer_data_end(tr, dp + sizeof(pattern));

      transfer_send(ctx, tr);
      ctx->bus_state = kUsbBulkOut;
      ctx->hostSt = HS_WAITACK;
      break;
    case HS_WAITACK:  // no actual ACK if Isochronous transfer
      ctx->wait = ctx->tick_bits + 32;
      ctx->hostSt = HS_REQDATA;
      break;
    case HS_REQDATA:
      if (ctx->tick_bits >= ctx->wait) {
        // Note: Isochronous transfers are not acknowledged and do not employ
        //       Data Toggle Synchronization
        if (expect_status && ctx->lastrxpid == USB_PID_ACK) {
          ctx->ep_out[endpoint].next_data =
              DATA_TOGGLE_ADVANCE(ctx->ep_out[endpoint].next_data);
        }

        transfer_token(tr, USB_PID_IN, ctx->dev_address, endpoint);
        transfer_send(ctx, tr);

        ctx->hostSt = HS_WAITDATA;
      }
      break;
    case HS_WAITDATA:
      ctx->wait = ctx->tick_bits + 40;  // HACK
      ctx->hostSt = HS_NEXTFRAME;
      printf("[usbdpi] testIso done\n");
    default:
      break;
  }
}

// Request IN. Get back DATA0/DATA1 or NAK.
//
// send_hi  -> also send OUT packet
// nak_data -> send NAK instead of ACK if there is data
void pollRX(usbdpi_ctx_t *ctx, uint8_t endpoint, bool send_hi, bool nak_data) {
  usbdpi_transfer_t *tr = ctx->sending;
  uint8_t *dp;
  switch (ctx->hostSt) {
    case HS_STARTFRAME:
      transfer_token(tr, USB_PID_IN, ctx->dev_address, endpoint);

      transfer_send(ctx, tr);
      ctx->bus_state = kUsbBulkInToken;
      ctx->hostSt = HS_WAIT_PKT;
      ctx->lastrxpid = 0;
      break;
    case HS_WAIT_PKT:
      // Wait max time for a response + packet
      ctx->wait = ctx->tick_bits + 18 + 8 + 8 + 64 * 8 + 16;
      ctx->hostSt = HS_ACKIFDATA;
      break;
    case HS_ACKIFDATA:
      if (ctx->bus_state == kUsbBulkInData) {
        // TODO - have we got a LFSR-generated data packet?
        if (ctx->lastrxpid != USB_PID_NAK) {
          transfer_status(ctx, tr, nak_data ? USB_PID_NAK : USB_PID_ACK);
        }
        ctx->hostSt = HS_SENDHI;
      } else if (ctx->tick_bits >= ctx->wait) {
        printf("[usbdpi] Timed out waiting for IN response\n");
        ctx->hostSt = HS_SENDHI;
      }
      break;
    case HS_SENDHI:
      if (send_hi) {
        transfer_token(tr, USB_PID_OUT, ctx->dev_address, endpoint);

        dp = transfer_data_start(tr, ctx->ep_out[endpoint].next_data, 0);
        dp[0] = 0x48;  // "H"
        dp[1] = 0x69;  // "i"
        dp[2] = 0x21;  // "!"
        transfer_data_end(tr, dp + 3);

        transfer_send(ctx, tr);
        ctx->wait = ctx->tick_bits + 532;  // HACK
        ctx->hostSt = HS_WAITACK;
      } else {
        ctx->hostSt = HS_NEXTFRAME;
      }
      break;
    case HS_WAITACK:
      if (ctx->tick_bits >= ctx->wait) {
        if (ctx->lastrxpid == USB_PID_ACK) {
          ctx->ep_out[endpoint].next_data =
              DATA_TOGGLE_ADVANCE(ctx->ep_out[endpoint].next_data);
        }
        ctx->hostSt = HS_NEXTFRAME;
      }
      break;
    default:
      break;
  }
}

// Test behavior in (non-)response to other device and unimplemented endpoints
void testUnimplEp(usbdpi_ctx_t *ctx, uint8_t pid, uint8_t device,
                  uint8_t endpoint) {
  usbdpi_transfer_t *tr = ctx->sending;
  uint8_t *dp;
  switch (ctx->hostSt) {
    case HS_STARTFRAME:
      if ((pid == USB_PID_SETUP) || (pid == USB_PID_OUT)) {
        transfer_token(tr, pid, device, endpoint);

        dp = transfer_data_start(tr, USB_PID_DATA0, 0);
        dp[0] = 0;  // h2d, std, device
        dp[1] = 5;  // set address
        dp[2] = 2;  // device address
        dp[3] = 0;
        // Trigger bitstuffing, technically the device
        // behavior is unspecified with wIndex != 0
        dp[4] = 0xFF;  // wIndex = 0xFF00
        dp[5] = 0;
        dp[6] = 0;  // wLength = 0
        dp[7] = 0;
        transfer_data_end(tr, dp + 8);

        transfer_send(ctx, tr);
        ctx->hostSt = HS_WAITACK;
        break;
      } else if (pid == USB_PID_IN) {
        transfer_token(tr, pid, device, endpoint);
        transfer_send(ctx, tr);

        // Since the endpoint is not implemented, the device should respond with
        // a STALL packet (not DATA0/1 or NAK).
        ctx->hostSt = HS_WAITACK;
        break;
      } else {
        ctx->hostSt = HS_NEXTFRAME;
        printf(
            "[usbdpi] testUnimplEp supports SETUP, OUT and IN transactions "
            "only\n");
        break;
      }
    case HS_WAITACK:
      // Note: We currently can't observe the responses sent by the device, but
      // usb_monitor() does log all transactions from host and device and does
      // some basic decoding.
      // Depending on the transaction type to unimplemented endpoints, we would
      // expect the following response:
      // - SETUP: no response (must be ignored by the device)
      // - OUT/IN: a STALL packet from the device
      ctx->wait = ctx->tick_bits + 32;  // HACK
      ctx->hostSt = HS_NEXTFRAME;
      printf("[usbdpi] testUnimplEp done\n");
      break;
    default:
      break;
  }
}

// Change host outputs
uint32_t set_driving(usbdpi_ctx_t *ctx, uint32_t d2p, uint32_t newval,
                     bool p2d_oe) {
  // Always maintain the current state of VBUS
  uint32_t driving = ctx->driving & P2D_SENSE;
  if (d2p & D2P_DNPU) {
    // Have dn pull-up, so must be flipping pins
    if (newval & P2D_DP) {
      driving |= P2D_DN | P2D_D;
    } else if (newval & P2D_DN) {
      driving |= P2D_DP;
    }
  } else {
    if (newval & P2D_DP) {
      driving |= P2D_DP | P2D_D;
    } else if (newval & P2D_DN) {
      driving |= P2D_DN;
    }
  }
  // Enable host output drivers?
  if (p2d_oe) {
    driving |= P2D_OE;
  }
  return driving;
}

// Optionally invert the signals the host is driving, according to bus
// configuration
uint32_t inv_driving(usbdpi_ctx_t *ctx, uint32_t d2p) {
  // works for either orientation
  return ctx->driving ^ (P2D_DP | P2D_DN | P2D_D);
}

uint8_t usbdpi_host_to_device(void *ctx_void, const svBitVecVal *usb_d2p) {
  usbdpi_ctx_t *ctx = (usbdpi_ctx_t *)ctx_void;
  assert(ctx);
  int d2p = usb_d2p[0];
  uint32_t last_driving = ctx->driving;
  int force_stat = 0;
  int dat;

  // The 48MHz clock runs at 4 times the bus clock for a full speed (12Mbps)
  // device
  //
  // TODO - vary the phase over the duration of the test to check device
  //        synchronization
  ctx->tick++;
  ctx->tick_bits = ctx->tick >> 2;
  if (ctx->tick & 3) {
    return ctx->driving;
  }

  // Monitor, analyse and record USB bus activity
  usb_monitor(ctx->mon, ctx->loglevel, ctx->tick_bits,
              (ctx->state != ST_IDLE) && (ctx->state != ST_GET), ctx->driving,
              d2p, &(ctx->lastrxpid));

  if (ctx->tick_bits == SENSE_AT) {
    ctx->driving |= P2D_SENSE;
  }

  if ((d2p & D2P_PU) == 0) {
    // In the event that the device disconnected, we must start anew in
    // anticipation of a reconnection
    bus_reset(ctx);
    ctx->driving = set_driving(ctx, d2p, 0, true);  // SE0
    ctx->recovery_time = ctx->tick + 4 * 48;
    return ctx->driving;
  }

  // Are we allowed to start transmitting yet; device recovery time elapsed?
  if (ctx->tick < ctx->recovery_time) {
    ctx->driving = set_driving(ctx, d2p, P2D_DP, false);  // J, but not driving
    ctx->state = ST_IDLE;
    ctx->frame_start = ctx->tick_bits;
    return ctx->driving;
  }

  // Time to commence a new bus frame?
  if ((ctx->tick_bits - ctx->frame_start) >= FRAME_INTERVAL) {
    if (ctx->state != ST_IDLE) {
      if (!ctx->framepend) {
        printf(
            "[usbdpi] frame 0x%x tick_bits 0x%x error state %d at frame 0x%x "
            "time\n",
            ctx->frame, ctx->tick, ctx->state, ctx->frame + 1);
      }
      ctx->framepend = true;
    } else {
      if (ctx->framepend) {
        printf("[usbdpi] frame 0x%x tick_bits 0x%x can send frame 0x%x SOF\n",
               ctx->frame, ctx->tick, ctx->frame + 1);
      }
      ctx->framepend = false;
      ctx->frame++;
      ctx->frame_start = ctx->tick_bits;

      if (ctx->step >= STEP_IDLE_START && ctx->step < STEP_IDLE_END) {
        // Test suspend behavior by dropping the SOF signalling
        ctx->state = ST_IDLE;
        printf("[usbdpi] idle frame 0x%x\n", ctx->frame);
      } else {
        // Ensure that a buffer is available for constructing a transfer
        usbdpi_transfer_t *tr = ctx->sending;
        if (!tr) {
          tr = transfer_alloc(ctx);
          assert(tr);

          ctx->sending = tr;
        }

        transfer_frame_start(ctx, tr, ctx->frame);
        ctx->state = ST_SYNC;
      }
      printf("[usbdpi] frame 0x%x tick_bits 0x%x CRC5 0x%x\n", ctx->frame,
             ctx->tick, CRC5(ctx->frame, 11));

      if (ctx->hostSt == HS_NEXTFRAME) {
        ctx->step = usbdpi_test_seq_next(ctx, ctx->step);
        ctx->num_tries = 0U;
        ctx->hostSt = HS_STARTFRAME;
      } else {
        // This normally means that we did not get the expected response to
        // a Control Transfer stage (Data/Status), so retry if we haven't
        // already exhausted our retry attempts.
        if (ctx->num_tries++ >= USBDPI_MAX_RETRIES) {
          ctx->num_tries = 0U;
          assert(!"USBDPI: no response to Control Transfer");
        } else {
          printf("[usbdpi] Warning: DPI Host not ready to start new frame\n");
          // For now we'll just start the Control Transfer again, because
          // this means sending a SETUP packet which should reset the device
          // behavior; later we may want to mimic more accurately a real
          // host.
          ctx->hostSt = HS_STARTFRAME;
        }
      }
    }
  }

  switch (ctx->state) {
    // Host state machine advances when the bit-level activity is idle
    case ST_IDLE: {
      // Ensure that a buffer is available for constructing a transfer
      if (!ctx->sending) {
        ctx->sending = transfer_alloc(ctx);
        assert(ctx->sending);
      }

      switch (ctx->step) {
        case STEP_BUS_RESET:
          // Note: this is a placeholder for the more proper Reset and Resume
          // signaling that has been implemented for suspend-resume testing;
          // this is sufficient for PinCfg test.
          switch (ctx->hostSt) {
            case HS_STARTFRAME:
              bus_reset(ctx);
              ctx->wait = ctx->tick_bits + 532;               // HACK
              ctx->driving = set_driving(ctx, d2p, 0, true);  // SE0
              ctx->hostSt = HS_NEXTFRAME;
              break;
            default:
              if (ctx->tick_bits >= ctx->wait) {
                // Let the bus float to Idle, undriven
                ctx->driving = set_driving(ctx, d2p, P2D_DP, false);  // J
              }
              ctx->hostSt = HS_NEXTFRAME;
              break;
          }
          break;

        case STEP_SET_DEVICE_ADDRESS:
          setDeviceAddress(ctx, USBDEV_ADDRESS);
          break;

          // TODO - an actual host issues a number of GET_DESCRIPTOR control/
          //        transfers to read descriptions of the configurations,
          //        interfaces and endpoints

        case STEP_GET_DEVICE_DESCRIPTOR:
          // Initially we fetch just the minimal descriptor length of 0x12U
          // bytes and the returned information will indicate the full length
          //
          // TODO - Set the descriptor length to the minimum because the DPI
          // model does not yet catch and report errors properly
          ctx->cfg_desc_len = 12U;
          getDescriptor(ctx, USB_DESC_TYPE_DEVICE, 0U, 0x12U);
          break;

        case STEP_GET_CONFIG_DESCRIPTOR:
          getDescriptor(ctx, USB_DESC_TYPE_CONFIGURATION, 0U, 0x9U);
          break;

        case STEP_GET_FULL_CONFIG_DESCRIPTOR: {
          uint16_t wLength = ctx->cfg_desc_len;
          if (wLength >= USBDEV_MAX_PACKET_SIZE) {
            // Note: getDescriptor cannot yet receive multiple packets
            wLength = USBDEV_MAX_PACKET_SIZE;
          }
          getDescriptor(ctx, USB_DESC_TYPE_CONFIGURATION, 0U, wLength);
        } break;

          // TODO - we must receive and respond to test configuration at some
          //        point; perhaps we can make the software advertise itself
          //        with different vendor/device combinations to indicate the
          //        testing we must do

        case STEP_SET_DEVICE_CONFIG:
          setDeviceConfiguration(ctx, 1);
          break;

        // Test configuration and status
        case STEP_GET_TEST_CONFIG:
          getTestConfig(ctx, 0x10U);
          break;

        case STEP_SET_TEST_STATUS:
          setTestStatus(ctx, ctx->test_status, ctx->test_msg);
          break;

          // These should be at 3 and 4 but the read needs the host
          // not to be sending (until skip fifo is implemented in in_pe engine)
          // so for now push later when things are quiet (could also adjust
          // hello_world to not use the uart until frame 4)

        case STEP_FIRST_READ:
          pollRX(ctx, ENDPOINT_SERIAL0, true, true);
          break;
        case STEP_READ_BAUD:
          readBaud(ctx, ENDPOINT_ZERO);
          break;
        case STEP_SECOND_READ:
          pollRX(ctx, ENDPOINT_SERIAL0, true, false);
          break;
        case STEP_SET_BAUD:
          setBaud(ctx, ENDPOINT_ZERO);
          break;
        case STEP_THIRD_READ:
          pollRX(ctx, ENDPOINT_SERIAL0, false, true);
          break;
        case STEP_TEST_ISO1:
          testIso(ctx);
          break;
        case STEP_TEST_ISO2:
          testIso(ctx);
          break;

        // Test each of SETUP, OUT and IN to an unimplemented endpoint
        case STEP_ENDPT_UNIMPL_SETUP:
          testUnimplEp(ctx, USB_PID_SETUP, ctx->dev_address,
                       ENDPOINT_UNIMPLEMENTED);
          break;
        case STEP_ENDPT_UNIMPL_OUT:
          testUnimplEp(ctx, USB_PID_OUT, ctx->dev_address,
                       ENDPOINT_UNIMPLEMENTED);
          break;
        case STEP_ENDPT_UNIMPL_IN:
          testUnimplEp(ctx, USB_PID_IN, ctx->dev_address,
                       ENDPOINT_UNIMPLEMENTED);
          break;

        // Test SETUP to a different device address
        case STEP_DEVICE_UK_SETUP:
          testUnimplEp(ctx, USB_PID_SETUP, UKDEV_ADDRESS, 1u);
          break;

        case STEP_STREAM_SERVICE:
          // After the initial testing of the (current) fixed DPI behavior,
          // we repeatedly try IN transfers, checking and scrambling any
          // data packets that we received before sending them straight back
          // to the device for software to check
          streams_service(ctx);
          break;

        default:
          if (ctx->step < STEP_IDLE_START || ctx->step >= STEP_IDLE_END) {
            pollRX(ctx, ENDPOINT_SERIAL0, false, false);
          }
          break;
      }
    } break;

    case ST_SYNC:
      dat = ((USB_SYNC & ctx->bit)) ? P2D_DP : P2D_DN;
      ctx->driving = set_driving(ctx, d2p, dat, true);
      force_stat = 1;
      ctx->bit <<= 1;
      if (ctx->bit == 0x100) {
        ctx->bit = 1;
        ctx->linebits = 1;  // The KK at end of SYNC counts for bit stuffing!
        ctx->state = ST_SEND;
      }
      break;

    case ST_SEND: {
      const usbdpi_transfer_t *sending = ctx->sending;
      assert(sending);
      if ((ctx->linebits & 0x3f) == 0x3f &&
          !INSERT_ERR_BITSTUFF) {  // sent 6 ones
        // bit stuff and force a transition
        ctx->driving = inv_driving(ctx, d2p);
        force_stat = 1;
        ctx->linebits = (ctx->linebits << 1);
      } else if (ctx->byte >= sending->num_bytes) {
        ctx->state = ST_EOP;
        ctx->driving = set_driving(ctx, d2p, 0, true);  // SE0
        ctx->bit = 1;
        force_stat = 1;
      } else {
        int nextbit = (sending->data[ctx->byte] & ctx->bit) ? 1 : 0;
        if (nextbit == 0) {
          ctx->driving = inv_driving(ctx, d2p);
        }
        ctx->linebits = (ctx->linebits << 1) | nextbit;
        force_stat = 1;
        ctx->bit <<= 1;
        if (ctx->bit == 0x100) {
          ctx->bit = 1;
          ctx->byte++;
          if (ctx->byte == sending->data_start) {
            ctx->state = ST_EOP0;
          }
        }
      }
    } break;

    case ST_EOP0:
      ctx->driving = set_driving(ctx, d2p, 0, true);  // SE0
      ctx->state = ST_EOP;
      break;

    case ST_EOP:  // SE0 SE0 J
      if (ctx->bit == 4) {
        ctx->driving = set_driving(ctx, d2p, P2D_DP, true);  // J
      }
      if (ctx->bit == 8) {
        const usbdpi_transfer_t *sending = ctx->sending;
        assert(sending);
        // Stop driving: host pulldown to SE0 unless there is a pullup on DP
        ctx->driving =
            set_driving(ctx, d2p, (d2p & D2P_PU) ? P2D_DP : 0, false);
        if (ctx->byte == sending->data_start) {
          ctx->bit = 1;
          ctx->state = ST_SYNC;
        } else {
          ctx->state = ST_IDLE;
        }
      }
      ctx->bit <<= 1;
      break;

    case ST_GET:
      // Device is driving the bus; nothing to do here
      break;

    default:
      assert(!"Unknown/invalid USBDPI drive state");
      break;
  }

  if ((ctx->loglevel & LOG_BIT) &&
      (force_stat || (ctx->driving != last_driving))) {
    usb_monitor_log(
        ctx->mon, "0x%-3x 0x-%8x              %s %s %s\n", ctx->frame,
        ctx->tick_bits, ctx->driving & P2D_SENSE ? "VBUS" : "    ",
        (ctx->state != ST_IDLE) ? decode_usb[(ctx->driving >> 1) & 3] : "ZZ ",
        (ctx->driving & P2D_D) ? "1" : "0");
  }
  return ctx->driving;
}

// Export some internal diagnostic state for visibility in waveforms
void usbdpi_diags(void *ctx_void, svBitVecVal *diags) {
  usbdpi_ctx_t *ctx = (usbdpi_ctx_t *)ctx_void;

  // Check for overflow, which would cause confusion in waveform interpretation.
  assert(ctx->state <= 0xfU);
  assert(ctx->hostSt <= 0x1fU);
  assert(ctx->bus_state <= 0x3fU);
  assert(ctx->step <= 0x7fU);

  diags[2] = usb_monitor_diags(ctx->mon);
  diags[1] =
      (ctx->step << 25) | (ctx->bus_state << 20) | (ctx->tick_bits >> 12);
  diags[0] = (ctx->tick_bits << 20) | ((ctx->frame & 0x7ffU) << 9) |
             ((ctx->hostSt & 0x1fU) << 4) | (ctx->state & 0xfU);
}

// Close the USBDPI model and release resources
void usbdpi_close(void *ctx_void) {
  usbdpi_ctx_t *ctx = (usbdpi_ctx_t *)ctx_void;
  if (!ctx) {
    return;
  }
  usb_monitor_fin(ctx->mon);
  free(ctx);
}
