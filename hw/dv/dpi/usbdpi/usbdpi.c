// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "usbdpi.h"

#ifdef __linux__
#include <pty.h>
#elif __APPLE__
#include <util.h>
#endif

#include <assert.h>
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>

// Historically the simulation started too fast to connect to all
// the fifos and terminals without loss of output. So a delay was added.
// Today the startup is slow enough this does not seem to be needed.
// In case things change again Im going to leave this behind a define
// for now, but if this continues not to be needed the code can be deleted.
// Uncomment next line if you need the delay
// #define NEED_SLEEP

static const char *st_states[] = {"ST_IDLE 0", "ST_SEND 1", "ST_GET 2",
                                  "ST_SYNC 3", "ST_EOP 4",  "ST_EOP0 5"};

static const char *hs_states[] = {
    "HS_STARTFRAME 0", "HS_WAITACK 1",   "HS_SET_DATASTAGE 2", "HS_DS_RXDATA 3",
    "HS_DS_SENDACK 4", "HS_DONEDADR 5",  "HS_REQDATA 6",       "HS_WAITDATA 7",
    "HS_SENDACK 8",    "HS_WAIT_PKT 9",  "HS_ACKIFDATA 10",    "HS_SENDHI 11",
    "HS_EMPTYDATA 12", "HS_WAITACK2 13", "HS_NEXTFRAME 14"};

void *usbdpi_create(const char *name, int loglevel) {
  struct usbdpi_ctx *ctx =
      (struct usbdpi_ctx *)calloc(1, sizeof(struct usbdpi_ctx));
  assert(ctx);

  ctx->tick = 0;
  ctx->frame = 0;
  ctx->framepend = 0;
  ctx->lastframe = 0;
  ctx->last_pu = 0;
  ctx->inframe = 4;
  ctx->state = ST_IDLE;
  ctx->driving = 0;
  ctx->hostSt = HS_NEXTFRAME;
  ctx->loglevel = loglevel;
  ctx->mon = monitor_usb_init();
  ctx->baudrate_set_successfully = 0;

  char cwd[PATH_MAX];
  char *cwd_rv;
  cwd_rv = getcwd(cwd, sizeof(cwd));
  assert(cwd_rv != NULL);

  int rv;

  // Monitor log file
  rv = snprintf(ctx->mon_pathname, PATH_MAX, "%s/%s.log", cwd, name);
  assert(rv <= PATH_MAX && rv > 0);
  ctx->mon_file = fopen(ctx->mon_pathname, "w");
  if (ctx->mon_file == NULL) {
    fprintf(stderr, "USB: Unable to open monitor file at %s: %s\n",
            ctx->mon_pathname, strerror(errno));
    return NULL;
  }
  // more useful for tail -f
  setlinebuf(ctx->mon_file);
  printf(
      "\nUSB: Monitor output file created at %s. Works well with tail:\n"
      "$ tail -f %s\n",
      ctx->mon_pathname, ctx->mon_pathname);

  return (void *)ctx;
}

const char *decode_usb[] = {"SE0", "0-K", "1-J", "SE1"};

void usbdpi_device_to_host(void *ctx_void, const svBitVecVal *usb_d2p) {
  struct usbdpi_ctx *ctx = (struct usbdpi_ctx *)ctx_void;
  assert(ctx);
  int d2p = usb_d2p[0];
  int dp, dn;
  int n;
  char obuf[MAX_OBUF];

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
      printf("USB: %4x %8d error state %s hs %s and device drives\n",
             ctx->frame, ctx->tick, st_states[ctx->state],
             hs_states[ctx->hostSt]);
    }
    ctx->state = ST_GET;
  } else {
    if (ctx->state == ST_GET) {
      ctx->state = ST_IDLE;
    }
  }

  if ((d2p & D2P_DNPU) && (d2p & D2P_DPPU)) {
    printf("USB: %4x %8d error both pullups are driven\n", ctx->frame,
           ctx->tick);
  }
  if ((d2p & D2P_PU) != ctx->last_pu) {
    n = snprintf(obuf, MAX_OBUF, "%4x %8d Pullup change to %s%s%s\n",
                 ctx->frame, ctx->tick, (d2p & D2P_DPPU) ? "DP Pulled up " : "",
                 (d2p & D2P_DNPU) ? "DN Pulled up " : "",
                 (d2p & D2P_TXMODE_SE) ? "SingleEnded" : "Differential");
    ssize_t written = fwrite(obuf, sizeof(char), (size_t)n, ctx->mon_file);
    assert(written == n);
    ctx->last_pu = d2p & D2P_PU;
  }
  if (d2p & D2P_TXMODE_SE) {
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
  } else {
    // "differential" mode uses D and SE0
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
  }

  if (ctx->loglevel & LOG_BIT) {
    const char *pullup = (d2p & D2P_PU) ? "PU" : "  ";
    const char *state =
        (ctx->state == ST_GET) ? decode_usb[dp << 1 | dn] : "ZZ ";

    n = snprintf(obuf, MAX_OBUF, "%4x %8d %s %s %s %x\n", ctx->frame, ctx->tick,
                 raw_str, pullup, state, d2p);
    ssize_t written = fwrite(obuf, sizeof(char), (size_t)n, ctx->mon_file);
    assert(written == n);
  }
}

// Note: start points to the PID which is not in the CRC
void add_crc16(uint8_t *dp, int start, int pos) {
  uint32_t crc = CRC16(dp + start + 1, pos - start - 1);
  dp[pos] = crc & 0xff;
  dp[pos + 1] = crc >> 8;
}

// Set device address (with null data stage)
void setDeviceAddress(struct usbdpi_ctx *ctx) {
  switch (ctx->hostSt) {
    case HS_STARTFRAME:
      ctx->state = ST_SYNC;
      ctx->bytes = 14;
      ctx->datastart = 3;
      ctx->byte = 0;
      ctx->bit = 1;
      // Setup PID and data to set device 2
      ctx->data[0] = USB_PID_SETUP;
      ctx->data[1] = 0;
      ctx->data[2] = 0 | CRC5(0, 11) << 3;
      ctx->data[3] = USB_PID_DATA0;
      if (INSERT_ERR_PID) {
        ctx->data[3] = 0xc4;
      }
      ctx->data[4] = 0;  // h2d, std, device
      ctx->data[5] = 5;  // set address
      ctx->data[6] = 2;  // device address
      ctx->data[7] = 0;
      // Trigger bitstuffing, technically the device
      // behaviour is unspecified with wIndex != 0
      ctx->data[8] = 0xFF;  // wIndex = 0xFF00
      ctx->data[9] = 0;
      ctx->data[10] = 0;  // wLength = 0
      ctx->data[11] = 0;
      add_crc16(ctx->data, ctx->datastart, 12);
      // ctx->data[12] = 0xEB; // pre-computed CRC16
      // ctx->data[13] = 0x16;
      if (INSERT_ERR_CRC) {
        // Flip the last CRC bit to emulate a CRC error
        ctx->data[13] = ctx->data[13] ^ 0x01;
      }
      ctx->hostSt = HS_WAITACK;
      break;
    case HS_WAITACK:
      ctx->wait = ctx->tick_bits + 532;  // HACK
      ctx->hostSt = HS_SET_DATASTAGE;
      break;
    case HS_SET_DATASTAGE:
      if (ctx->tick_bits == ctx->wait) {
        ctx->state = ST_SYNC;
        ctx->bytes = 3;
        ctx->datastart = -1;
        ctx->byte = 0;
        ctx->bit = 1;
        ctx->data[0] = USB_PID_IN;
        ctx->data[1] = 0;
        ctx->data[2] = 0 | CRC5(0, 11) << 3;
        ctx->hostSt = HS_DS_RXDATA;
      }
      break;
    case HS_DS_RXDATA:
      ctx->wait = ctx->tick_bits + 24;  // HACK -- 2 bytes
      ctx->hostSt = HS_DS_SENDACK;
      break;
    case HS_DS_SENDACK:
      if (ctx->tick_bits >= ctx->wait) {
        ctx->state = ST_SYNC;
        ctx->bytes = 1;
        ctx->datastart = -1;
        ctx->byte = 0;
        ctx->bit = 1;
        ctx->data[0] = USB_PID_ACK;
        ctx->hostSt = HS_NEXTFRAME;
        printf("[usbdpi] setDeviceAddress done\n");
      }
      break;
    default:
      break;
  }
}

// Get Descriptor
void readDescriptor(struct usbdpi_ctx *ctx) {
  switch (ctx->hostSt) {
    case HS_STARTFRAME:
      ctx->state = ST_SYNC;
      ctx->bytes = 14;
      ctx->datastart = 3;
      ctx->byte = 0;
      ctx->bit = 1;
      ctx->data[0] = USB_PID_SETUP;
      ctx->data[1] = 2;
      ctx->data[2] = 0 | CRC5(2, 11) << 3;
      ctx->data[3] = USB_PID_DATA0;
      ctx->data[4] = 0x80;  // d2h, std, device
      ctx->data[5] = 6;     // get descr
      ctx->data[6] = 0;     // index 0
      ctx->data[7] = 1;     // type device
      ctx->data[8] = 0;     // wIndex = 0
      ctx->data[9] = 0;
      ctx->data[10] = 0x12;  // wLength = 18
      ctx->data[11] = 0;
      add_crc16(ctx->data, ctx->datastart, 12);
      // ctx->data[12] = 0xE0; // pre-computed CRC32
      // ctx->data[13] = 0xF4;
      ctx->hostSt = HS_WAITACK;
      break;
    case HS_WAITACK:
      ctx->wait = ctx->tick_bits + 532;  // HACK
      ctx->hostSt = HS_REQDATA;
      break;
    case HS_REQDATA:
      if (ctx->tick_bits == ctx->wait) {
        ctx->state = ST_SYNC;
        ctx->bytes = 3;
        ctx->datastart = -1;
        ctx->byte = 0;
        ctx->bit = 1;
        ctx->data[0] = USB_PID_IN;
        ctx->data[1] = 2;
        ctx->data[2] = 0 | CRC5(2, 11) << 3;
        ctx->hostSt = HS_WAITDATA;
      }
      break;
    case HS_WAITDATA:
      ctx->wait = ctx->tick_bits + 200;  // HACK
      ctx->hostSt = HS_SENDACK;
      break;
    case HS_SENDACK:
      if (ctx->tick_bits == ctx->wait) {
        ctx->state = ST_SYNC;
        ctx->bytes = 1;
        ctx->datastart = -1;
        ctx->byte = 0;
        ctx->bit = 1;
        ctx->data[0] = USB_PID_ACK;
        ctx->hostSt = HS_NEXTFRAME;
        printf("[usbdpi] readDescriptor done\n");
      }
      break;
    default:
      break;
  }
}

// Get Baud
void readBaud(struct usbdpi_ctx *ctx) {
  switch (ctx->hostSt) {
    case HS_STARTFRAME:
      ctx->state = ST_SYNC;
      ctx->bytes = 14;
      ctx->datastart = 3;
      ctx->byte = 0;
      ctx->bit = 1;
      ctx->data[0] = USB_PID_SETUP;
      ctx->data[1] = 0x82;
      ctx->data[2] = 0 | CRC5(0x82, 11) << 3;
      ctx->data[3] = USB_PID_DATA0;
      ctx->data[4] = 0xc2;  // d2h, vendor, endpoint
      ctx->data[5] = 2;     // get baud
      ctx->data[6] = 0;     // index 0
      ctx->data[7] = 0;     // type device
      ctx->data[8] = 0;     // wIndex = 0
      ctx->data[9] = 0;
      ctx->data[10] = 0x2;  // wLength = 2
      ctx->data[11] = 0;
      add_crc16(ctx->data, ctx->datastart, 12);
      // ctx->data[12] = 0x10; // pre-computed CRC32
      // ctx->data[13] = 0xDD;
      ctx->hostSt = HS_WAITACK;
      break;
    case HS_WAITACK:
      ctx->wait = ctx->tick_bits + 32;  // HACK
      ctx->hostSt = HS_REQDATA;
      break;
    case HS_REQDATA:
      if (ctx->tick_bits == ctx->wait) {
        ctx->state = ST_SYNC;
        ctx->bytes = 3;
        ctx->datastart = -1;
        ctx->byte = 0;
        ctx->bit = 1;
        ctx->data[0] = USB_PID_IN;
        ctx->data[1] = 0x82;
        ctx->data[2] = 0 | CRC5(0x82, 11) << 3;
        ctx->hostSt = HS_WAITDATA;
      }
      break;
    case HS_WAITDATA:
      ctx->wait = ctx->tick_bits + 200;  // HACK
      ctx->hostSt = HS_SENDACK;
      break;
    case HS_SENDACK:
      if (ctx->tick_bits == ctx->wait) {
        ctx->state = ST_SYNC;
        ctx->bytes = 1;
        ctx->datastart = -1;
        ctx->byte = 0;
        ctx->bit = 1;
        ctx->data[0] = USB_PID_ACK;
        ctx->hostSt = HS_EMPTYDATA;
      }
      break;
    case HS_EMPTYDATA:
      ctx->state = ST_SYNC;
      ctx->bytes = 6;
      ctx->datastart = 3;
      ctx->byte = 0;
      ctx->bit = 1;
      ctx->data[0] = USB_PID_OUT;
      ctx->data[1] = 0x82;
      ctx->data[2] = 0 | CRC5(0x82, 11) << 3;
      ctx->data[3] = USB_PID_DATA1;
      ctx->data[4] = 0x0;  // pre-computed CRC32
      ctx->data[5] = 0x0;
      ctx->hostSt = HS_WAITACK2;
      break;
    case HS_WAITACK2:
      ctx->wait = ctx->tick_bits + 32;  // HACK
      ctx->hostSt = HS_NEXTFRAME;
      printf("[usbdpi] readBaud done\n");
      break;
    default:
      break;
  }
}

// Set Baud
void setBaud(struct usbdpi_ctx *ctx) {
  switch (ctx->hostSt) {
    case HS_STARTFRAME:
      ctx->state = ST_SYNC;
      ctx->bytes = 14;
      ctx->datastart = 3;
      ctx->byte = 0;
      ctx->bit = 1;
      ctx->data[0] = USB_PID_SETUP;
      ctx->data[1] = 0x82;
      ctx->data[2] = 0 | CRC5(0x82, 11) << 3;
      ctx->data[3] = USB_PID_DATA0;
      ctx->data[4] = 0x42;  // h2d, vendor, endpoint
      ctx->data[5] = 3;     // set baud
      ctx->data[6] = 96;    // index 0
      ctx->data[7] = 0;     // type device
      ctx->data[8] = 0;     // wIndex = 0
      ctx->data[9] = 0;
      ctx->data[10] = 0;  // wLength = 0
      ctx->data[11] = 0;
      add_crc16(ctx->data, ctx->datastart, 12);
      // ctx->data[12] = 0x00; // pre-computed CRC32
      // ctx->data[13] = 0xBD;
      ctx->hostSt = HS_WAITACK;
      break;
    case HS_WAITACK:
      ctx->wait = ctx->tick_bits + 32;  // HACK
      ctx->hostSt = HS_REQDATA;
      break;
    case HS_REQDATA:
      if (ctx->tick_bits == ctx->wait) {
        ctx->state = ST_SYNC;
        ctx->bytes = 3;
        ctx->datastart = -1;
        ctx->byte = 0;
        ctx->bit = 1;
        ctx->data[0] = USB_PID_IN;
        ctx->data[1] = 0x82;
        ctx->data[2] = 0 | CRC5(0x82, 11) << 3;
        ctx->hostSt = HS_WAITDATA;
      }
      break;
    case HS_WAITDATA:
      ctx->wait = ctx->tick_bits + 40;  // HACK
      ctx->hostSt = HS_SENDACK;
      break;
    case HS_SENDACK:
      if (ctx->tick_bits >= ctx->wait) {
        ctx->state = ST_SYNC;
        ctx->bytes = 1;
        ctx->datastart = -1;
        ctx->byte = 0;
        ctx->bit = 1;
        ctx->data[0] = USB_PID_ACK;
        ctx->hostSt = HS_NEXTFRAME;
        ctx->baudrate_set_successfully = 1;
        printf("[usbdpi] setBaud done\n");
      }
      break;
    default:
      break;
  }
}

// Test the ischronous transfers (without ACKs)
void testIso(struct usbdpi_ctx *ctx) {
  switch (ctx->hostSt) {
    case HS_STARTFRAME:
      ctx->state = ST_SYNC;
      ctx->bytes = 14;
      ctx->datastart = 3;
      ctx->byte = 0;
      ctx->bit = 1;
      ctx->data[0] = USB_PID_OUT;
      ctx->data[1] = 0x82;
      ctx->data[2] = 1 | CRC5(0x182, 11) << 3;

      ctx->data[3] = USB_PID_DATA0;
      ctx->data[4] = 0x42;  // h2d, vendor, endpoint
      ctx->data[5] = 3;     // set baud
      ctx->data[6] = 96;    // index 0
      ctx->data[7] = 0;     // type device
      ctx->data[8] = 0;     // wIndex = 0
      ctx->data[9] = 0;
      ctx->data[10] = 0;  // wLength = 0
      ctx->data[11] = 0;

      add_crc16(ctx->data, ctx->datastart, 12);
      // ctx->data[12] = 0x00; // pre-computed CRC32
      // ctx->data[13] = 0xBD;
      ctx->hostSt = HS_WAITACK;
      break;
    case HS_WAITACK:  // no actual ACK
      ctx->wait = ctx->tick_bits + 32;
      ctx->hostSt = HS_REQDATA;
      break;
    case HS_REQDATA:
      if (ctx->tick_bits == ctx->wait) {
        ctx->state = ST_SYNC;
        ctx->bytes = 3;
        ctx->datastart = -1;
        ctx->byte = 0;
        ctx->bit = 1;
        ctx->data[0] = USB_PID_IN;
        ctx->data[1] = 0x82;
        ctx->data[2] = 1 | CRC5(0x0182, 11) << 3;
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

// Request IN. Get back NAK or DATA0/DATA1.
// sendHi -> also send OUT packet
// nakData -> send NAK instead of ACK if there is data
void pollRX(struct usbdpi_ctx *ctx, int sendHi, int nakData) {
  switch (ctx->hostSt) {
    case HS_STARTFRAME:
      ctx->state = ST_SYNC;
      ctx->bytes = 3;
      ctx->datastart = -1;
      ctx->byte = 0;
      ctx->bit = 1;
      ctx->data[0] = USB_PID_IN;
      ctx->data[1] = 0x82;
      ctx->data[2] = 0x00 | CRC5(0x0082, 11) << 3;
      ctx->hostSt = HS_WAIT_PKT;
      ctx->lastrxpid = 0;
      break;
    case HS_WAIT_PKT:
      if ((ctx->lastrxpid) && (ctx->lastrxpid != USB_PID_IN)) {
        ctx->wait = ctx->tick_bits + 32;  // Expect to be busy then
        ctx->hostSt = HS_ACKIFDATA;
      }
      break;
    case HS_ACKIFDATA:
      if (ctx->tick_bits >= ctx->wait) {
        if (ctx->lastrxpid != USB_PID_NAK) {
          // device sent data so ACK it
          // TODO check DATA0 vs DATA1
          ctx->state = ST_SYNC;
          ctx->bytes = 1;
          ctx->datastart = -1;
          ctx->byte = 0;
          ctx->bit = 1;
          ctx->data[0] = nakData ? USB_PID_NAK : USB_PID_ACK;
        }
        if (sendHi) {
          ctx->hostSt = HS_SENDHI;
        } else {
          ctx->hostSt = HS_NEXTFRAME;
          ctx->inframe = ctx->frame;
        }
      }
      break;
    case HS_SENDHI:
      ctx->state = ST_SYNC;
      ctx->bytes = 9;
      ctx->datastart = 3;
      ctx->byte = 0;
      ctx->bit = 1;
      ctx->data[0] = USB_PID_OUT;
      ctx->data[1] = 0x82;
      ctx->data[2] = 0 | CRC5(0x82, 11) << 3;
      ctx->data[3] = USB_PID_DATA0;
      ctx->data[4] = 0x48;  // "H"
      ctx->data[5] = 0x69;  // "i"
      ctx->data[6] = 0x21;  // "!"
      add_crc16(ctx->data, ctx->datastart, 7);
      // ctx->data[7] = 0xE0; // pre-computed CRC16
      // ctx->data[8] = 0x61;
      ctx->inframe = ctx->frame;
      ctx->hostSt = HS_NEXTFRAME;  // Device will ACK
      break;
    default:
      break;
  }
}

// Test unimplemented endpoints
void testUnimplEp(struct usbdpi_ctx *ctx, uint8_t pid) {
  switch (ctx->hostSt) {
    case HS_STARTFRAME:
      if ((pid == USB_PID_SETUP) || (pid == USB_PID_OUT)) {
        ctx->state = ST_SYNC;
        ctx->bytes = 14;
        ctx->datastart = 3;
        ctx->byte = 0;
        ctx->bit = 1;
        // The bytes are transmitted LSB to MSB
        ctx->data[0] = pid;
        ctx->data[1] =
            ((UNIMPL_EP_ID & 0x1) << 7) | 0x2;  // endpoint ID LSB, address
        ctx->data[2] = CRC5((UNIMPL_EP_ID << 7) | 0x2, 11) << 3 |
                       ((UNIMPL_EP_ID >> 1) & 0x7);  // CRC, endpoint ID MSBs

        ctx->data[3] = USB_PID_DATA0;
        ctx->data[4] = 0;  // h2d, std, device
        ctx->data[5] = 5;  // set address
        ctx->data[6] = 2;  // device address
        ctx->data[7] = 0;
        // Trigger bitstuffing, technically the device
        // behaviour is unspecified with wIndex != 0
        ctx->data[8] = 0xFF;  // wIndex = 0xFF00
        ctx->data[9] = 0;
        ctx->data[10] = 0;  // wLength = 0
        ctx->data[11] = 0;
        add_crc16(ctx->data, ctx->datastart, 12);
        ctx->hostSt = HS_WAITACK;
        break;
      } else if (pid == USB_PID_IN) {
        ctx->state = ST_SYNC;
        ctx->bytes = 3;
        ctx->datastart = 0;
        ctx->byte = 0;
        ctx->bit = 1;
        // The bytes are transmitted LSB to MSB
        ctx->data[0] = pid;
        ctx->data[1] =
            ((UNIMPL_EP_ID & 0x1) << 7) | 0x2;  // endpoint ID LSB, address
        ctx->data[2] = CRC5((UNIMPL_EP_ID << 7) | 0x2, 11) << 3 |
                       ((UNIMPL_EP_ID >> 1) & 0x7);  // CRC, endpoint ID MSBs
        // Since the endpoint is not implemented, the device will respond with a
        // STALL packet (not DATA0/1 or NAK).
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
      // monitor_usb() does log all transactions from host and device and does
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

int set_driving(struct usbdpi_ctx *ctx, int d2p, int newval) {
  if (d2p & D2P_DNPU) {
    if (d2p & D2P_TXMODE_SE) {
      return (ctx->driving & P2D_SENSE) | ((newval & P2D_DP) ? P2D_DN : 0) |
             ((newval & P2D_DN) ? P2D_DP : 0);
    }
    if (newval & (P2D_DP | P2D_DN)) {
      // sets single ended lines to K after swapping
      return (ctx->driving & P2D_SENSE) | P2D_DP |
             ((newval & P2D_DN) ? P2D_D : 0);
    }
    // SE0 so D could be anything (make it 1 after swapping)
    return ctx->driving & P2D_SENSE;
  }
  if (d2p & D2P_TXMODE_SE) {
    return (ctx->driving & P2D_SENSE) | newval;
  }
  if (newval & (P2D_DP | P2D_DN)) {
    // sets single ended lines to K
    return (ctx->driving & P2D_SENSE) | P2D_DN |
           ((newval & P2D_DP) ? P2D_D : 0);
  }
  // SE0 so D could be anything (make it 1)
  return (ctx->driving & P2D_SENSE) | P2D_D;
}

int inv_driving(struct usbdpi_ctx *ctx, int d2p) {
  // works for either orientation
  return ctx->driving ^ ((d2p & D2P_TXMODE_SE) ? (P2D_DP | P2D_DN) : P2D_D);
}

char usbdpi_host_to_device(void *ctx_void, const svBitVecVal *usb_d2p) {
  struct usbdpi_ctx *ctx = (struct usbdpi_ctx *)ctx_void;
  assert(ctx);
  int d2p = usb_d2p[0];
  uint32_t last_driving = ctx->driving;
  int force_stat = 0;
  int dat;

  if (ctx->tick == 0) {
    int i;
#ifdef NEED_SLEEP
    for (i = 7; i > 0; i--) {
      printf("Sleep %d...\n", i);
      sleep(1);
    }
#endif
  }
  ctx->tick++;
  ctx->tick_bits = ctx->tick >> 2;
  if (ctx->tick & 3) {
    return ctx->driving;
  }

  monitor_usb(ctx->mon, ctx->mon_file, ctx->loglevel, ctx->tick,
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

  if ((ctx->tick_bits - ctx->lastframe) >= FRAME_INTERVAL) {
    if (ctx->state != ST_IDLE) {
      if (ctx->framepend == 0) {
        printf("USB: %4x %8d error state %d at frame %d time\n", ctx->frame,
               ctx->tick, ctx->state, ctx->frame + 1);
      }
      ctx->framepend = 1;
    } else {
      if (ctx->framepend == 1) {
        printf("USB: %4x %8d can send frame %d SOF\n", ctx->frame, ctx->tick,
               ctx->frame + 1);
      }
      ctx->framepend = 0;
      ctx->frame++;
      ctx->lastframe = ctx->tick_bits;

      if (ctx->frame >= 20 && ctx->frame < 30) {
        // Test suspend
        ctx->state = ST_IDLE;
        printf("Idle frame %d\n", ctx->frame);
      } else {
        ctx->state = ST_SYNC;
        ctx->bytes = 3;
        ctx->datastart = -1;
        ctx->byte = 0;
        ctx->bit = 1;
        ctx->data[0] = USB_PID_SOF;
        ctx->data[1] = ctx->frame & 0xff;
        ctx->data[2] =
            ((ctx->frame & 0x700) >> 8) | (CRC5(ctx->frame & 0x7ff, 11) << 3);
      }
      printf("USB: %8d frame 0x%x CRC5 0x%x\n", ctx->tick, ctx->frame,
             CRC5(ctx->frame, 11));
      if (ctx->hostSt == HS_NEXTFRAME) {
        ctx->hostSt = HS_STARTFRAME;
      }
    }
  }
  switch (ctx->state) {
    case ST_IDLE:
      switch (ctx->frame) {
        case 1:
          setDeviceAddress(ctx);
          break;
        case 2:
          readDescriptor(ctx);
          break;
        // These should be at 3 and 4 but the read needs the host
        // not to be sending (until skip fifo is implemented in in_pe engine)
        // so for now push later when things are quiet (could also adjust
        // hello_world to not use the uart until frame 4)
        case 10:
          readBaud(ctx);
          break;
        case 15:
          setBaud(ctx);
          break;
        case 17:
          testIso(ctx);
          break;
        case 18:
          testIso(ctx);
          break;
        case 20:
          testUnimplEp(ctx, USB_PID_SETUP);
          break;
        case 21:
          testUnimplEp(ctx, USB_PID_OUT);
          break;
        case 22:
          testUnimplEp(ctx, USB_PID_IN);
          break;
        default:
          if (ctx->frame > ctx->inframe &&
              !(ctx->frame >= 23 && ctx->frame < 33)) {
            pollRX(ctx, (ctx->frame == 9) || (ctx->frame == 14),
                   ((ctx->frame == 16) || (ctx->frame == 9)));
          }
      }
      break;

    case ST_SYNC:
      dat = ((USB_SYNC & ctx->bit)) ? P2D_DP : P2D_DN;
      ctx->driving = set_driving(ctx, d2p, dat);
      force_stat = 1;
      ctx->bit <<= 1;
      if (ctx->bit == 0x100) {
        ctx->bit = 1;
        ctx->linebits = 0;
        ctx->state = ST_SEND;
      }
      break;

    case ST_SEND:
      if ((ctx->linebits & 0x3f) == 0x3f &&
          !INSERT_ERR_BITSTUFF) {  // sent 6 ones
        // bit stuff and force a transition
        ctx->driving = inv_driving(ctx, d2p);
        force_stat = 1;
        ctx->linebits = (ctx->linebits << 1);
      } else if (ctx->byte >= ctx->bytes) {
        ctx->state = ST_EOP;
        ctx->driving = set_driving(ctx, d2p, 0);  // SE0
        ctx->bit = 1;
        force_stat = 1;
      } else {
        int nextbit;
        nextbit = (ctx->data[ctx->byte] & ctx->bit) ? 1 : 0;
        if (nextbit == 0) {
          ctx->driving = inv_driving(ctx, d2p);
        }
        ctx->linebits = (ctx->linebits << 1) | nextbit;
        force_stat = 1;
        ctx->bit <<= 1;
        if (ctx->bit == 0x100) {
          ctx->bit = 1;
          ctx->byte++;
          if (ctx->byte == ctx->datastart) {
            ctx->state = ST_EOP0;
          }
        }
      }
      break;

    case ST_EOP0:
      ctx->driving = set_driving(ctx, d2p, 0);  // SE0
      ctx->state = ST_EOP;
      break;

    case ST_EOP:  // SE0 SE0 J
      if (ctx->bit == 4) {
        ctx->driving = set_driving(ctx, d2p, P2D_DP);  // J
      }
      if (ctx->bit == 8) {
        // Stop driving: host pulldown to SE0 unless there is a pullup on DP
        ctx->driving = set_driving(ctx, d2p, (d2p & D2P_PU) ? P2D_DP : 0);
        if (ctx->byte == ctx->datastart) {
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
    int n;
    char obuf[MAX_OBUF];

    n = snprintf(
        obuf, MAX_OBUF, "%4x %8d              %s %s %s\n", ctx->frame,
        ctx->tick, ctx->driving & P2D_SENSE ? "VBUS" : "    ",
        (ctx->state != ST_IDLE) ? decode_usb[(ctx->driving >> 1) & 3] : "ZZ ",
        (ctx->driving & P2D_D) ? "1" : "0");
    ssize_t written = fwrite(obuf, sizeof(char), (size_t)n, ctx->mon_file);
    assert(written == n);
  }
  return ctx->driving;
}

void usbdpi_close(void *ctx_void) {
  struct usbdpi_ctx *ctx = (struct usbdpi_ctx *)ctx_void;
  if (!ctx) {
    return;
  }
  fclose(ctx->mon_file);
  free(ctx);
}
