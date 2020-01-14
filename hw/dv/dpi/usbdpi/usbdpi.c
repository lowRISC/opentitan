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
  rv = snprintf(ctx->fifo_pathname, PATH_MAX, "%s/%s", cwd, name);
  assert(rv <= PATH_MAX && rv > 0);

  // Delete the file if it still exists (simulation crashed)
  rv = unlink(ctx->fifo_pathname);

  rv = mkfifo(ctx->fifo_pathname, 0644);  // writes are not supported currently
  if (rv != 0) {
    fprintf(stderr, "USB: Unable to create FIFO at %s: %s\n",
            ctx->fifo_pathname, strerror(errno));
    return NULL;
  }

  ctx->fifo_fd = open(ctx->fifo_pathname, O_RDWR);
  if (ctx->fifo_fd < 0) {
    fprintf(stderr, "USB: Unable to open FIFO at %s: %s\n", ctx->fifo_pathname,
            strerror(errno));
    return NULL;
  }

  printf(
      "\n"
      "USB: FIFO pipe created at %s. Run\n"
      "$ cat %s\n"
      "to observe the output.\n",
      ctx->fifo_pathname, ctx->fifo_pathname);
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
    for (i = 0; i < 5; i++) {
      raw_str[5 - i - 1] = !!(d2p & (1 << i)) + '0';
    }
  }
  raw_str[D2P_BITS] = 0;

  if (d2p & (D2P_DP_EN | D2P_DN_EN)) {
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

  dp = (((d2p & D2P_DP_EN) && (d2p & D2P_DP)) ||
        (!(d2p & D2P_DP_EN) && (d2p & D2P_PU)))
           ? 1
           : 0;

  dn = ((d2p & D2P_DN_EN) && (d2p & D2P_DN)) ? 1 : 0;

  if (ctx->loglevel & LOG_BIT) {
    n = snprintf(obuf, MAX_OBUF, "%4x %8d %s %s %s\n", ctx->frame, ctx->tick,
                 raw_str, (d2p & D2P_PU) ? "PU" : "  ",
                 (ctx->state == ST_GET) ? decode_usb[dp << 1 | dn] : "ZZ ");
    ssize_t written = write(ctx->fifo_fd, obuf, n);
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
      ctx->data[4] = 0x48;
      ctx->data[5] = 0x69;
      ctx->data[6] = 0x21;
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

char usbdpi_host_to_device(void *ctx_void, const svBitVecVal *usb_d2p) {
  struct usbdpi_ctx *ctx = (struct usbdpi_ctx *)ctx_void;
  assert(ctx);
  int d2p = usb_d2p[0];
  uint32_t last_driving = ctx->driving;
  int force_stat = 0;
  int dat;

  if (ctx->tick == 0) {
    int i;
    for (i = 7; i > 0; i--) {
      printf("Sleep %d...\n", i);
      sleep(1);
    }
  }
  ctx->tick++;
  ctx->tick_bits = ctx->tick >> 2;
  if (ctx->tick & 3) {
    return ctx->driving;
  }

  monitor_usb(ctx->mon, ctx->fifo_fd, ctx->loglevel, ctx->tick,
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
        default:
          if (ctx->frame > ctx->inframe &&
              !(ctx->frame >= 20 && ctx->frame < 30)) {
            pollRX(ctx, (ctx->frame == 9) || (ctx->frame == 14),
                   ((ctx->frame == 16) || (ctx->frame == 9)));
          }
      }
      break;

    case ST_SYNC:
      dat = ((USB_SYNC & ctx->bit)) ? P2D_DP : P2D_DN;
      ctx->driving = (ctx->driving & P2D_SENSE) | dat;
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
        ctx->driving ^= (P2D_DP | P2D_DN);
        force_stat = 1;
        ctx->linebits = (ctx->linebits << 1);
      } else if (ctx->byte >= ctx->bytes) {
        ctx->state = ST_EOP;
        ctx->driving = ctx->driving & P2D_SENSE;  // SE0
        ctx->bit = 1;
        force_stat = 1;
      } else {
        int nextbit;
        nextbit = (ctx->data[ctx->byte] & ctx->bit) ? 1 : 0;
        if (nextbit == 0) {
          ctx->driving ^= (P2D_DP | P2D_DN);
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
      ctx->driving = ctx->driving & P2D_SENSE;  // SE0
      ctx->state = ST_EOP;
      break;

    case ST_EOP:  // SE0 SE0 J
      if (ctx->bit == 4) {
        ctx->driving = (ctx->driving & P2D_SENSE) | P2D_DP;  // J
      }
      if (ctx->bit == 8) {
        ctx->driving = (d2p & D2P_PU) ? (ctx->driving & P2D_SENSE) | P2D_DP
                                      :               // Z + pullup
                           ctx->driving & P2D_SENSE;  // z without pullup = SE0
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
        obuf, MAX_OBUF, "%4x %8d              %s %s\n", ctx->frame, ctx->tick,
        ctx->driving & P2D_SENSE ? "VBUS" : "    ",
        (ctx->state != ST_IDLE) ? decode_usb[(ctx->driving >> 1) & 3] : "ZZ ");
    ssize_t written = write(ctx->fifo_fd, obuf, n);
    assert(written == n);
  }
  return ctx->driving;
}

void usbdpi_close(void *ctx_void) {
  struct usbdpi_ctx *ctx = (struct usbdpi_ctx *)ctx_void;
  if (!ctx) {
    return;
  }
  int rv;
  rv = close(ctx->fifo_fd);
  if (rv != 0) {
    printf("USB: Failed to close FIFO: %s\n", strerror(errno));
  }
  rv = unlink(ctx->fifo_pathname);
  if (rv != 0) {
    printf("USB: Failed to unlink FIFO file at %s: %s\n", ctx->fifo_pathname,
           strerror(errno));
  }
  free(ctx);
}
