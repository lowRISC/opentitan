// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifdef __linux__
#include <pty.h>
#elif __APPLE__
#include <util.h>
#endif

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

#include "usb_monitor.h"
#include "usbdpi.h"

// Seed numbers for the LFSR generators in each transfer direction
#define USBTST_LFSR_SEED 0x10U
#define USBDPI_LFSR_SEED 0x9BU

// Historically the simulation started too fast to connect to all
// the fifos and terminals without loss of output. So a delay was added.
// Today the startup is slow enough this does not seem to be needed.
// In case things change again Im going to leave this behind a define
// for now, but if this continues not to be needed the code can be deleted.
// Uncomment next line if you need the delay
// #define NEED_SLEEP

// TODO - introduce setting of device configuration; initially we're refactoring
// without
//        changing/extending behaviour
// #define SET_DEV_CONFIG

static const char *st_states[] = {"ST_IDLE 0", "ST_SEND 1", "ST_GET 2",
                                  "ST_SYNC 3", "ST_EOP 4",  "ST_EOP0 5"};

static const char *hs_states[] = {
    "HS_STARTFRAME 0", "HS_WAITACK 1",   "HS_SET_DATASTAGE 2", "HS_DS_RXDATA 3",
    "HS_DS_SENDACK 4", "HS_DONEDADR 5",  "HS_REQDATA 6",       "HS_WAITDATA 7",
    "HS_SENDACK 8",    "HS_WAIT_PKT 9",  "HS_ACKIFDATA 10",    "HS_SENDHI 11",
    "HS_EMPTYDATA 12", "HS_WAITACK2 13", "HS_NEXTFRAME 14"};

// Request IN transfer. Get back NAK or DATA0/DATA1.
static void pollRX(usbdpi_ctx_t *ctx, uint8_t endpoint, bool bSendHi,
                   bool bNakData);
// Get Baud
static void readBaud(usbdpi_ctx_t *ctx);
// Get Descriptor
static void readDescriptor(usbdpi_ctx_t *ctx);
// Set Baud
static void setBaud(usbdpi_ctx_t *ctx);
// Set device address (with null data stage)
static void setDeviceAddress(usbdpi_ctx_t *ctx, uint8_t dev_addr);
// Set device configuration
#if SET_DEVICE_CONFIG
static void setDeviceConfiguration(usbdpi_ctx_t *ctx);
#endif

// Try to send OUT transfer. Optionally expect Status packet (eg. ACK|NAK) in
// response
static void tryTX(usbdpi_ctx_t *ctx, bool bExpectStatus);
// Test the ischronous transfers (without ACKs)
// static void testIso(usbdpi_ctx_t *ctx);
#define testIso(ctx) tryTX((ctx), false)

/**
 * Create a USB DPI instance, returning a 'chandle' for later use
 */
void *usbdpi_create(const char *name, int loglevel) {
  // Use calloc for zero-initialisation
  usbdpi_ctx_t *ctx = (usbdpi_ctx_t *)calloc(1, sizeof(usbdpi_ctx_t));
  USBDPI_ASSERT(ctx);

  // Note: calloc has initialised most of the fields for us
  // ctx->tick = 0;
  // ctx->tick_bits = 0;
  // ctx->frame = 0;
  // ctx->framepend = 0;
  // ctx->lastframe = 0;
  // ctx->last_pu = 0;
  // ctx->driving = 0;
  // ctx->baudrate_set_successfully = 0;

  // Note: we hold off polling for IN transfers until after we've
  //       performed some basic iniitalisation and the polling-based host
  //       software is ready to respond
  //
  // TODO - change this to a proper state machine to sequence the traffic
  ctx->inframe = 4U;

  ctx->state = ST_IDLE;
  ctx->hostSt = HS_NEXTFRAME;
  ctx->loglevel = loglevel;

  // NOTE: it would perhaps be preferable to move the file handling into the
  //       monitor itself, but at the moment we use its file handle here...
  char cwd[FILENAME_MAX];
  char *cwd_rv;
  cwd_rv = getcwd(cwd, sizeof(cwd));
  USBDPI_ASSERT(cwd_rv != NULL);

  // Monitor log file
  int rv = snprintf(ctx->mon_pathname, FILENAME_MAX, "%s/%s.log", cwd, name);
  USBDPI_ASSERT(rv <= FILENAME_MAX && rv > 0);

  ctx->mon = usb_monitor_init(ctx->mon_pathname);

  // Prepare the transfer descriptors for use
  usb_transfer_setup(ctx);

  return (void *)ctx;
}

const char *decode_usb[] = {"SE0", "0-K", "1-J", "SE1"};

void usbdpi_device_to_host(void *ctx_void, const svBitVecVal *usb_d2p) {
  int d2p = usb_d2p[0];
  int dp, dn;

  usbdpi_ctx_t *ctx = (usbdpi_ctx_t *)ctx_void;
  USBDPI_ASSERT(ctx);

  char raw_str[D2P_BITS + 1];
  {
    int i;
    for (i = 0; i < D2P_BITS; i++) {
      raw_str[D2P_BITS - i - 1] = d2p & (1 << i) ? '1' : '0';
    }
  }
  raw_str[D2P_BITS] = 0;

  if (d2p & (D2P_DP_EN | D2P_DN_EN | D2P_D_EN)) {
    if (ctx->state == ST_SEND) {
      printf(
          "USBDPI: frame 0x%x tick_bits 0x%x error state %s hs %s and device "
          "drives\n",
          ctx->frame, ctx->tick_bits, st_states[ctx->state],
          hs_states[ctx->hostSt]);
    }
    ctx->state = ST_GET;
  } else {
    if (ctx->state == ST_GET) {
      ctx->state = ST_IDLE;
    }
  }

  if ((d2p & D2P_DNPU) && (d2p & D2P_DPPU)) {
    printf("USBDPI: frame 0x%x tick_bits 0x%x error both pullups are driven\n",
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
      // DN pullup would say DP and DN are swapped
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

  if (ctx->loglevel & LOG_BIT) {
    const char *pullup = (d2p & D2P_PU) ? "PU" : "  ";
    const char *state =
        (ctx->state == ST_GET) ? decode_usb[dp << 1 | dn] : "ZZ ";
    usb_monitor_log(ctx->mon, "0x%-3x 0x%-8x %s %s %s %x\n", ctx->frame,
                    ctx->tick_bits, raw_str, pullup, state, d2p);
  }

  // Device-to-Host EOP
  if (ctx->state == ST_GET && dp == 0 && dp == 0) {
    switch (ctx->bus_state) {
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
      case kUsbBulkOut:
        ctx->bus_state = kUsbBulkOutAck;
        break;
      case kUsbBulkInToken:
        ctx->bus_state = kUsbBulkInData;
      default:;
    }
  }
}

// Set device address (with null data stage)
void setDeviceAddress(usbdpi_ctx_t *ctx, uint8_t dev_addr) {
  usbdpi_transfer_t *tr = ctx->sending;
  uint8_t *dp;
  switch (ctx->hostSt) {
    case HS_STARTFRAME:
      // Setting device address, uses address 0 initially
      transfer_token(tr, USB_PID_SETUP, 0, ENDPOINT_ZERO);

      dp = transfer_data_start(tr, USB_PID_DATA0, 8);
      if (INSERT_ERR_PID) {
        *(dp - 1) = 0xc4U;
      }
      dp[0] = 0;  // h2d, std, device
      dp[1] = USB_REQ_SET_ADDRESS;
      dp[2] = dev_addr;  // device address
      dp[3] = 0;
      // Trigger bitstuffing, technically the device
      // behaviour is unspecified with wIndex != 0
      dp[4] = 0xFF;  // wIndex = 0xFF00
      dp[5] = 0;
      dp[6] = 0;  // wLength = 0
      dp[7] = 0;
      transfer_data_end(tr, dp + 8);
      if (INSERT_ERR_CRC) {
        // Flip the last CRC bit to emulate a CRC error
        dp[9] ^= 0x01U;
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
        printf("[usbdpi] setDeviceAddress done\n");
      }
      break;
    default:
      break;
  }
}

#if SET_DEV_CONFIG
// Set device configuration
void setDeviceConfiguration(uspdpi_ctx_t *ctx) {}
#endif

// Get Descriptor
void readDescriptor(usbdpi_ctx_t *ctx) {
  usbdpi_transfer_t *tr = ctx->sending;
  uint8_t *dp;
  switch (ctx->hostSt) {
    case HS_STARTFRAME:
      transfer_token(tr, USB_PID_SETUP, ctx->dev_address, ENDPOINT_ZERO);

      dp = transfer_data_start(tr, USB_PID_DATA0, 0);
      dp[0] = 0x80;  // d2h, std, device
      dp[1] = USB_REQ_GET_DESCRIPTOR;
      dp[2] = 0;  // index 0
      dp[3] = 1;  // type device
      dp[4] = 0;  // wIndex = 0
      dp[5] = 0;
      dp[6] = 0x12;  // wLength = 18
      dp[7] = 0;
      transfer_data_end(tr, dp + 8);

      transfer_send(ctx, tr);
      ctx->bus_state = kUsbControlSetup;
      ctx->hostSt = HS_WAITACK;
      break;
    case HS_WAITACK:
      ctx->wait = ctx->tick_bits + 532;  // HACK
      ctx->hostSt = HS_REQDATA;
      break;
    case HS_REQDATA:
      if (ctx->bus_state == kUsbControlSetupAck &&
          ctx->tick_bits >= ctx->wait) {
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
      if (ctx->tick_bits >= ctx->wait) {
        printf("[usbdpi] Timed out waiting for device\n");
        ctx->hostSt = HS_NEXTFRAME;
        ctx->bus_state = kUsbIdle;
      }
      if (ctx->bus_state == kUsbControlDataInData) {
        transfer_token(tr, USB_PID_ACK, ctx->dev_address, ENDPOINT_ZERO);

        transfer_send(ctx, tr);

        ctx->bus_state = kUsbControlDataInAck;
        ctx->hostSt = HS_WAIT_PKT;

        ctx->wait = ctx->tick_bits + 200;  // HACK
      }
      break;
    case HS_WAIT_PKT:
      if (ctx->tick_bits >= ctx->wait) {
        ctx->hostSt = HS_EMPTYDATA;
      }
      break;
    case HS_EMPTYDATA:
      // Transmit OUT transaction with no DATA packet
      transfer_token(tr, USB_PID_OUT, ctx->dev_address, ENDPOINT_ZERO);

      transfer_send(ctx, tr);
      ctx->bus_state = kUsbControlStatusOut;
      ctx->hostSt = HS_WAITACK2;

      ctx->wait = ctx->tick_bits + 200;  // HACK
      break;
    case HS_WAITACK2:
      if (ctx->tick_bits >= ctx->wait ||
          ctx->bus_state == kUsbControlStatusOutAck) {
        ctx->hostSt = HS_NEXTFRAME;
      }
      break;
    default:
      break;
  }
}

// Get Baud
void readBaud(usbdpi_ctx_t *ctx) {
  usbdpi_transfer_t *tr = ctx->sending;
  uint8_t *dp;
  switch (ctx->hostSt) {
    case HS_STARTFRAME:
      transfer_token(tr, USB_PID_SETUP, ctx->dev_address, ENDPOINT_SERIAL0);

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

      // TODO - why are we not setting bus_state here too?
      transfer_send(ctx, tr);
      ctx->hostSt = HS_WAITACK;
      break;
    case HS_WAITACK:
      ctx->wait = ctx->tick_bits + 32;  // HACK
      ctx->hostSt = HS_REQDATA;
      break;
    case HS_REQDATA:
      if (ctx->tick_bits >= ctx->wait) {
        transfer_token(tr, USB_PID_IN, ctx->dev_address, ENDPOINT_SERIAL0);

        transfer_send(ctx, tr);
        ctx->hostSt = HS_WAITDATA;
      }
      break;
    case HS_WAITDATA:
      ctx->wait = ctx->tick_bits + 200;  // HACK
      ctx->hostSt = HS_SENDACK;
      break;
    case HS_SENDACK:
      if (ctx->tick_bits >= ctx->wait) {
        transfer_status(ctx, tr, USB_PID_ACK);
        ctx->hostSt = HS_EMPTYDATA;
      }
      break;
    case HS_EMPTYDATA:
      // Transmit OUT transaction with zero-length DATA packet
      transfer_token(tr, USB_PID_OUT, ctx->dev_address, ENDPOINT_SERIAL0);
      if (INSERT_ERR_DATA_TOGGLE) {
        // NOTE: This raises a LinkOutErr on the USBDEV because it is expecting
        //       DATA0
        dp = transfer_data_start(tr, USB_PID_DATA1, 0);
      } else {
        dp = transfer_data_start(tr, USB_PID_DATA0, 0);
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
        ctx->hostSt = HS_NEXTFRAME;
        printf("[usbdpi] readBaud done\n");
      }
      break;
    default:
      break;
  }
}

// Set Baud
void setBaud(usbdpi_ctx_t *ctx) {
  usbdpi_transfer_t *tr = ctx->sending;
  uint8_t *dp;
  switch (ctx->hostSt) {
    case HS_STARTFRAME:
      transfer_token(tr, USB_PID_SETUP, ctx->dev_address, ENDPOINT_SERIAL0);

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
      ctx->hostSt = HS_WAITACK;
      break;
    case HS_WAITACK:
      ctx->wait = ctx->tick_bits + 32;  // HACK
      ctx->hostSt = HS_REQDATA;
      break;
    case HS_REQDATA:
      if (ctx->tick_bits >= ctx->wait) {
        transfer_token(tr, USB_PID_IN, ctx->dev_address, ENDPOINT_SERIAL0);

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

// Try OUT transfer to the device, optionally expecting a Status
//   packet (eg. ACK|NAK) in response; this is not expected for
//   Isochronous transfers
void tryTX(usbdpi_ctx_t *ctx, bool bExpectStatus) {
  usbdpi_transfer_t *tr = ctx->sending;
  uint8_t *dp;
  switch (ctx->hostSt) {
    case HS_STARTFRAME:
      transfer_token(tr, USB_PID_OUT, ctx->dev_address, ENDPOINT_ISOCHRONOUS);

      // TODO - DATA toggle synchronization
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
      ctx->hostSt = HS_WAITACK;
      break;
    case HS_WAITACK:  // no actual ACK
      ctx->wait = ctx->tick_bits + 32;
      ctx->hostSt = HS_REQDATA;
      break;
    case HS_REQDATA:
      if (ctx->tick_bits >= ctx->wait) {
        transfer_token(tr, USB_PID_IN, ctx->dev_address, ENDPOINT_ISOCHRONOUS);
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
// bSendHi  -> also send OUT packet
// bNakData -> send NAK instead of ACK if there is data
void pollRX(usbdpi_ctx_t *ctx, uint8_t endpoint, bool bSendHi, bool bNakData) {
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
      if (ctx->tick_bits >= ctx->wait) {
        printf("[usbdpi] Timed out waiting for IN response\n");
        ctx->hostSt = HS_SENDHI;
      } else if (ctx->bus_state == kUsbBulkInData) {
        if (ctx->lastrxpid != USB_PID_NAK) {
          transfer_status(ctx, tr, bNakData ? USB_PID_NAK : USB_PID_ACK);
        }
        ctx->hostSt = HS_SENDHI;
      }
      break;
    case HS_SENDHI:
      if (bSendHi) {
        transfer_token(tr, USB_PID_OUT, ctx->dev_address, endpoint);

        dp = transfer_data_start(tr, USB_PID_DATA0, 0);
        dp[0] = 0x48;  // "H"
        dp[1] = 0x69;  // "i"
        dp[2] = 0x21;  // "!"
        transfer_data_end(tr, dp + 3);

        transfer_send(ctx, tr);
      }
      ctx->inframe = ctx->frame;
      ctx->hostSt = HS_NEXTFRAME;  // Device will ACK
      break;
    default:
      break;
  }
}

// Test behaviour in (non-)response to other device and unimplemented endpoints
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
        // behaviour is unspecified with wIndex != 0
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

// Change DP and DN outputs from host
int set_driving(usbdpi_ctx_t *ctx, int d2p, int newval) {
  // Always maintain the current state of VBUS
  int driving = ctx->driving & P2D_SENSE;
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
  return driving;
}

int inv_driving(usbdpi_ctx_t *ctx, int d2p) {
  // works for either orientation
  return ctx->driving ^ (P2D_DP | P2D_DN | P2D_D);
}

uint8_t usbdpi_host_to_device(void *ctx_void, const svBitVecVal *usb_d2p) {
  usbdpi_ctx_t *ctx = (usbdpi_ctx_t *)ctx_void;
  USBDPI_ASSERT(ctx);
  int d2p = usb_d2p[0];
  uint32_t last_driving = ctx->driving;
  int force_stat = 0;
  int dat;

  if (ctx->tick == 0) {
#ifdef NEED_SLEEP
    int i;
    for (i = 7; i > 0; i--) {
      printf("USBDPI Sleep %d...\n", i);
      sleep(1);
    }
#endif
  }
  ctx->tick++;

  // The 48MHz clock runs at 4 times the bus clock for a full speed (12Mbps)
  // device
  ctx->tick_bits = ctx->tick >> 2;
  if (ctx->tick & 3) {
    return ctx->driving;
  }

  // Monitor, analyse and record USB bus activity
  usb_monitor(ctx->mon, ctx->loglevel, ctx->tick,
              (ctx->state != ST_IDLE) && (ctx->state != ST_GET), ctx->driving,
              d2p, &(ctx->lastrxpid));

  if (ctx->tick_bits == SENSE_AT) {
    ctx->driving |= P2D_SENSE;
  }

  if ((d2p & D2P_PU) == 0) {
    ctx->recovery_time = ctx->tick + 4 * 48;
    return ctx->driving;
  }

  if (ctx->tick < ctx->recovery_time) {
    ctx->lastframe = ctx->tick_bits;
    return ctx->driving;
  }

  // Time to commence a new bus frame?
  if ((ctx->tick_bits - ctx->lastframe) >= FRAME_INTERVAL) {
    if (ctx->state != ST_IDLE) {
      if (ctx->framepend == 0) {
        printf(
            "USBDPI: frame 0x%x tick_bits 0x%x error state %d at frame 0x%x "
            "time\n",
            ctx->frame, ctx->tick, ctx->state, ctx->frame + 1);
      }
      ctx->framepend = 1;
    } else {
      if (ctx->framepend == 1) {
        printf("USBDPI: frame 0x%x tick_bits 0x%x can send frame 0x%x SOF\n",
               ctx->frame, ctx->tick, ctx->frame + 1);
      }
      ctx->framepend = 0;
      ctx->frame++;
      ctx->lastframe = ctx->tick_bits;

      // TODO - modify this accordingly when separating the frame number and the
      //        STEP_ state machine
      if (ctx->frame >= 20 && ctx->frame < 30) {
        // Test suspend
        ctx->state = ST_IDLE;
        printf("Idle frame 0x%x\n", ctx->frame);
      } else {
        // Ensure that a buffer is available for constructing a transfer
        usbdpi_transfer_t *tr = ctx->sending;
        if (!tr) {
          tr = transfer_alloc(ctx);
          USBDPI_ASSERT(tr);

          ctx->sending = tr;
        }

        transfer_frame_start(ctx, tr, ctx->frame);
        ctx->state = ST_SYNC;
      }
      printf("USBDPI: frame 0x%x tick_bits 0x%x CRC5 0x%x\n", ctx->frame,
             ctx->tick, CRC5(ctx->frame, 11));
      if (ctx->hostSt == HS_NEXTFRAME) {
        ctx->hostSt = HS_STARTFRAME;
      }
    }
  }
  switch (ctx->state) {
    case ST_IDLE: {
      // Ensure that a buffer is available for constructing a transfer
      usbdpi_transfer_t *tr = ctx->sending;
      if (!tr) {
        tr = transfer_alloc(ctx);
        USBDPI_ASSERT(tr);
        ctx->sending = tr;
      }

      // TODO - test step remains equivalent to the frame number for now; fixed
      //        timing, not yet responsive to the device/sw behaviour
      ctx->step = ctx->frame;

      switch (ctx->step) {
        case STEP_SET_DEVICE_ADDRESS:
          setDeviceAddress(ctx, USBDEV_ADDRESS);
          ctx->dev_address = USBDEV_ADDRESS;
          break;

        case STEP_READ_DESCRIPTOR:
          readDescriptor(ctx);
          break;

          // FIXME: Should have SET_CONFIGURATION here, else non-default
          // endpoints should be disabled.
          //
          // case STEP_SET_DEVICE_CONFIG:
          //   setDeviceConfiguration(ctx);
          //   break;

          // These should be at 3 and 4 but the read needs the host
          // not to be sending (until skip fifo is implemented in in_pe engine)
          // so for now push later when things are quiet (could also adjust
          // hello_world to not use the uart until frame 4)

        case STEP_FIRST_READ:
          pollRX(ctx, 1, true, true);
          break;
        case STEP_READ_BAUD:
          readBaud(ctx);
          break;

        case STEP_SECOND_READ:
          pollRX(ctx, 1, true, false);
          break;
        case STEP_SET_BAUD:
          setBaud(ctx);
          break;
        case STEP_THIRD_READ:
          pollRX(ctx, 1, false, true);
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
        case STEP_DEVICE_UK_SETUP:
          testUnimplEp(ctx, USB_PID_SETUP, UKDEV_ADDRESS, 1U);
          break;

        default:
          if (ctx->frame > ctx->inframe &&
              !(ctx->frame >= STEP_IDLE_START && ctx->frame < STEP_IDLE_END)) {
            // For frames 33 onwards, we just poll reading
            //   and try writing on alternate frames for now...
            if (ctx->frame & 1U)
              pollRX(ctx, 1, false, false);
            else
              tryTX(ctx, true);
          }
      }
    } break;

    case ST_SYNC:
      dat = ((USB_SYNC & ctx->bit)) ? P2D_DP : P2D_DN;
      ctx->driving = set_driving(ctx, d2p, dat);
      force_stat = 1;
      ctx->bit <<= 1;
      if (ctx->bit == 0x100) {
        ctx->bit = 1;
        ctx->linebits = 1;  // The KK at end of SYNC counts for bit stuffing!
        ctx->state = ST_SEND;
      }
      break;

    case ST_SEND: {
      usbdpi_transfer_t *sending = ctx->sending;
      USBDPI_ASSERT(sending);
      if ((ctx->linebits & 0x3f) == 0x3f &&
          !INSERT_ERR_BITSTUFF) {  // sent 6 ones
        // bit stuff and force a transition
        ctx->driving = inv_driving(ctx, d2p);
        force_stat = 1;
        ctx->linebits = (ctx->linebits << 1);
      } else if (ctx->byte >= sending->num_bytes) {
        ctx->state = ST_EOP;
        ctx->driving = set_driving(ctx, d2p, 0);  // SE0
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
      ctx->driving = set_driving(ctx, d2p, 0);  // SE0
      ctx->state = ST_EOP;
      break;

    case ST_EOP:  // SE0 SE0 J
      if (ctx->bit == 4) {
        ctx->driving = set_driving(ctx, d2p, P2D_DP);  // J
      }
      if (ctx->bit == 8) {
        usbdpi_transfer_t *sending = ctx->sending;
        USBDPI_ASSERT(sending);
        // Stop driving: host pulldown to SE0 unless there is a pullup on DP
        ctx->driving = set_driving(ctx, d2p, (d2p & D2P_PU) ? P2D_DP : 0);
        if (ctx->byte == sending->data_start) {
          ctx->bit = 1;
          ctx->state = ST_SYNC;
        } else {
          ctx->state = ST_IDLE;
        }
      }
      ctx->bit <<= 1;
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

  diags[1] = (ctx->bus_state << 20) | (ctx->tick_bits >> 12);
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
