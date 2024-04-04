// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <assert.h>
#include <errno.h>
#include <stdarg.h>
#include <stdio.h>
#include <string.h>

#include "usb_utils.h"
#include "usbdpi.h"

// USB monitor state
typedef enum { MS_IDLE = 0, MS_GET_PID, MS_GET_BYTES } usb_monitor_state_t;

// Current driver of the USB
typedef enum { M_NONE = 0, M_HOST, M_DEVICE } usbmon_driver_t;

#define SE0 0
#define DK 1
#define DJ 2

#define MON_BYTES_SIZE 1024

// Number of bytes in max output buffer line
#define MAX_OBUF 80

/**
 * USB monitor context
 */
struct usb_monitor_ctx {
  /**
   * Log file
   */
  FILE *file;
  /**
   * Monitor state, reflecting the current state of the USB
   */
  usb_monitor_state_t state;
  /**
   * Current bus driver
   */
  usbmon_driver_t driver;
  uint32_t pu;
  int line;
  int rawbits;
  int bits;
  int needbits;
  int sopAt;
  uint8_t lastpid;
  /**
   * USB data callback
   */
  usb_monitor_data_callback_t data_callback;
  /**
   * Context for data callback
   */
  void *data_ctx;
  /**
   * Byte offset of the next byte to be collected in the data buffer
   */
  uint8_t byte;
  /**
   * Buffer of collected bytes
   */
  uint8_t bytes[MON_BYTES_SIZE + 2];
};

// Invoke the USB data callback function, if registered
static inline void data_callback(usb_monitor_ctx_t *mon,
                                 usbmon_data_type_t type, uint8_t d) {
  if (mon->data_callback) {
    mon->data_callback(mon->data_ctx, type, d);
  }
}

/**
 * Create and initialize a USB monitor instance
 */
usb_monitor_ctx_t *usb_monitor_init(const char *filename,
                                    usb_monitor_data_callback_t data_cb,
                                    void *data_ctx) {
  usb_monitor_ctx_t *mon =
      (usb_monitor_ctx_t *)calloc(1, sizeof(usb_monitor_ctx_t));
  assert(mon);

  mon->state = MS_IDLE;
  mon->driver = M_NONE;
  mon->pu = 0;
  mon->line = 0;

  // Retain details of the device reception callback
  mon->data_callback = data_cb;
  mon->data_ctx = data_ctx;

  mon->file = fopen(filename, "w");
  if (!mon->file) {
    fprintf(stderr, "USBDPI: Unable to open monitor file at %s: %s\n", filename,
            strerror(errno));
    free(mon);
    return NULL;
  }

  // more useful for tail -f
  setlinebuf(mon->file);
  printf(
      "\nUSBDPI: Monitor output file created at %s. Works well with tail:\n"
      "$ tail -f %s\n",
      filename, filename);

  return mon;
}

/**
 * Finalize a USB monitor
 */
void usb_monitor_fin(usb_monitor_ctx_t *mon) {
  fclose(mon->file);
  free(mon);
}

/**
 * Append a formatted message to the USB monitor log file
 */
void usb_monitor_log(usb_monitor_ctx_t *ctx, const char *fmt, ...) {
  char obuf[MAX_OBUF];
  va_list ap;
  va_start(ap, fmt);
  int n = vsnprintf(obuf, MAX_OBUF, fmt, ap);
  va_end(ap);
  size_t written = fwrite(obuf, sizeof(char), (size_t)n, ctx->file);
  assert(written == (size_t)n);
}

#define DR_SIZE 128
static char dr[DR_SIZE];
char *pid_2data(int pid, unsigned char d0, unsigned char d1) {
  int comp_crc = CRC5((d1 & 7) << 8 | d0, 11);
  const char *crcok = (comp_crc == d1 >> 3) ? "OK" : "BAD";

  switch (pid) {
    case USB_PID_SOF:
      snprintf(dr, DR_SIZE, "SOF %03x (CRC5 %02x %s)", (d1 & 7) << 8 | d0,
               d1 >> 3, crcok);
      break;

    case USB_PID_SETUP:
    case USB_PID_OUT:
    case USB_PID_IN:
      snprintf(dr, DR_SIZE, "%s %d.%d (CRC5 %02x %s)", decode_pid(pid),
               d0 & 0x7f, (d1 & 7) << 1 | d0 >> 7, d1 >> 3, crcok);
      break;

    case USB_PID_DATA0:
    case USB_PID_DATA1:
      snprintf(dr, DR_SIZE, "%s %02x, %02x (%s)", decode_pid(pid), d0, d1,
               (d0 | d1) ? "CRC16 BAD" : "NULL");
      break;

    // Validate and log other PIDs
    default:
      if (((pid >> 4) ^ 0xf) == (pid & 0xf)) {
        snprintf(dr, DR_SIZE, "%s %02x, %02x (CRC5 %s)", decode_pid(pid), d0,
                 d1, crcok);
      } else {
        snprintf(dr, DR_SIZE, "BAD PID %s %02x, %02x (CRC5 %s)",
                 decode_pid(pid), d0, d1, crcok);
      }
      break;
  }
  return dr;
}

/**
 * Per-cycle monitoring of the USB
 */
void usb_monitor(usb_monitor_ctx_t *mon, int loglevel, uint32_t tick_bits,
                 bool hdrive, uint32_t p2d, uint32_t d2p, uint8_t *lastpid) {
  bool log = ((loglevel & 0x2) != 0);
  bool compact = ((loglevel & 0x1) != 0);

  assert(mon);

  // Ascertain state of D+/D- pair; these may have been swapped in some use
  // cases, but we can ascertain this by looking at the pull-up enables.
  // The DUT is a full speed device so the pull up should be on D+
  int dp, dn;
  if ((d2p & D2P_DP_EN) || (d2p & D2P_DN_EN) || (d2p & D2P_D_EN)) {
    if (hdrive) {
      fprintf(mon->file, "mon: %8d: Bus clash\n", tick_bits);
    }
    if (d2p & D2P_TX_USE_D_SE0) {
      // Single-ended mode uses D and SE0
      if ((d2p & D2P_SE0) || !(d2p & D2P_D_EN)) {
        // SE0 state, both D+ and D- are low
        dp = 0;
        dn = 0;
      } else {
        // Normal single-ended data transmission
        dp = (d2p & D2P_D) ? 1 : 0;
        dn = (d2p & D2P_D) ? 0 : 1;
      }
    } else {
      dp = ((d2p & D2P_DP_EN) && (d2p & D2P_DP)) ? 1 : 0;
      dn = ((d2p & D2P_DN_EN) && (d2p & D2P_DN)) ? 1 : 0;
    }
    mon->driver = M_DEVICE;
  } else if (hdrive) {
    if (d2p & D2P_RX_ENABLE) {
      if (p2d & (P2D_DP | P2D_DN)) {
        dp = (p2d & P2D_D) ? 1 : 0;
        dn = (p2d & P2D_D) ? 0 : 1;
      } else {
        dp = 0;
        dn = 0;
      }
    } else {
      dp = (p2d & P2D_DP) ? 1 : 0;
      dn = (p2d & P2D_DN) ? 1 : 0;
    }
    mon->driver = M_HOST;
  } else {
    if ((mon->driver != M_NONE) || (mon->pu != (d2p & D2P_PU))) {
      if (log) {
        if (d2p & D2P_PU) {
          fprintf(mon->file, "mon: %8d: Idle, FS resistor (d2p 0x%x)\n",
                  tick_bits, d2p);
        } else {
          fprintf(mon->file, "mon: %8d: Idle, SE0\n", tick_bits);
        }
      }
      mon->driver = M_NONE;
      mon->pu = (d2p & D2P_PU);
    }
    mon->line = 0;
    return;
  }
  // If the DN pullup is there then swap
  if (d2p & D2P_DNPU) {
    int tmp = dp;
    dp = dn;
    dn = tmp;
  }
  // Collect D+/D- state
  mon->line = (mon->line << 2) | dp << 1 | dn;

  // SYNC at start of packet
  if (mon->state == MS_IDLE) {
    if ((mon->line & 0xfff) == ((DK << 10) | (DJ << 8) | (DK << 6) | (DJ << 4) |
                                (DK << 2) | (DK << 0))) {
      if (log) {
        fprintf(mon->file, "mon: %8d: (%c) SOP\n", tick_bits,
                mon->driver == M_HOST ? 'H' : 'D');
      }
      mon->sopAt = tick_bits;
      mon->state = MS_GET_PID;
      mon->needbits = 8;
      data_callback(mon, UsbMon_DataType_Sync, 0U);
    }
    return;
  }

  // EOP detection, calculate and check the CRC16 on any data field
  if ((mon->line & 0x3f) == ((SE0 << 4) | (SE0 << 2) | (DJ << 0))) {
    if ((log || compact) && (mon->state == MS_GET_BYTES) && (mon->byte > 0)) {
      uint32_t pkt_crc16, comp_crc16;

      if (compact && mon->byte == 2) {
        fprintf(mon->file, "mon: %8d -- %8d: (%c) SOP, PID %s, EOP\n",
                mon->sopAt, tick_bits, mon->driver == M_HOST ? 'H' : 'D',
                pid_2data(mon->lastpid, mon->bytes[0], mon->bytes[1]));
      } else if (compact && mon->byte == 1) {
        fprintf(mon->file, "mon: %8d -- %8d: (%c) SOP, PID %s %02x EOP\n",
                mon->sopAt, tick_bits, mon->driver == M_HOST ? 'H' : 'D',
                decode_pid(mon->lastpid), mon->bytes[0]);
      } else {
        if (compact) {
          fprintf(mon->file, "mon: %8d -- %8d: (%c) SOP, PID %s, EOP\n",
                  mon->sopAt, tick_bits, mon->driver == M_HOST ? 'H' : 'D',
                  decode_pid(mon->lastpid));
        }
        fprintf(mon->file, "mon:     %s:\n",
                mon->driver == M_HOST ? "h->d" : "d->h");
        comp_crc16 = CRC16(mon->bytes, mon->byte - 2);
        pkt_crc16 =
            mon->bytes[mon->byte - 2] | (mon->bytes[mon->byte - 1] << 8);

        dump_bytes(mon->file, "mon:          ", mon->bytes, mon->byte - 2, 0u);

        // Display the received CRC16 value
        fprintf(mon->file, "\nmon:          (CRC16 %02x %02x",
                mon->bytes[mon->byte - 2], mon->bytes[mon->byte - 1]);
        if (comp_crc16 == pkt_crc16) {
          fprintf(mon->file, "%s OK)\n",
                  (mon->byte == MON_BYTES_SIZE) ? "..." : "");
        } else {
          fprintf(mon->file,
                  "%s BAD)\nmon:           CRC16 %04x BAD expected %04x\n",
                  (mon->byte == MON_BYTES_SIZE) ? "..." : "", pkt_crc16,
                  comp_crc16);
        }
      }
    } else if (compact) {
      fprintf(mon->file, "mon: %8d -- %8d: (%c) SOP, PID %s EOP\n", mon->sopAt,
              tick_bits, mon->driver == M_HOST ? 'H' : 'D',
              decode_pid(mon->lastpid));
    }
    if (log) {
      fprintf(mon->file, "mon: %8d: (%c) EOP\n", tick_bits,
              mon->driver == M_HOST ? 'H' : 'D');
    }
    mon->state = MS_IDLE;
    data_callback(mon, UsbMon_DataType_EOP, 0U);
    return;
  }

  int newbit = (((mon->line & 0xc) >> 2) == (mon->line & 0x3)) ? 1 : 0;
  mon->rawbits = (mon->rawbits << 1) | newbit;
  if ((mon->rawbits & 0x7e) == 0x7e) {
    if (newbit == 1) {
      fprintf(mon->file, "mon: %8d: (%c) Bitstuff error, got 1 after 0x%x\n",
              tick_bits, mon->driver == M_HOST ? 'H' : 'D', mon->rawbits);
    }
    /* Ignore bit stuff bit */
    return;
  }
  mon->bits = (mon->bits >> 1) | (newbit << 7);
  mon->needbits--;
  if (mon->needbits) {
    return;
  }

  // Complete byte received
  switch (mon->state) {
    case MS_GET_PID: {
      // Any byte for which the upper nibble is not the exact complement
      // of the lower nibble is invalid
      uint8_t pid = (uint8_t)mon->bits;
      if (((pid ^ 0xf0) >> 4) ^ (pid & 0x0f)) {
        if (log) {
          fprintf(mon->file, "mon: %8d: (%c) BAD PID 0x%x\n", tick_bits,
                  mon->driver == M_HOST ? 'H' : 'D', pid);
        }
      } else {
        *lastpid = pid;
        mon->lastpid = pid;
        if (log) {
          fprintf(mon->file, "mon: %8d: (%c) PID %s (0x%x)\n", tick_bits,
                  mon->driver == M_HOST ? 'H' : 'D', decode_pid(pid), pid);
        }
      }
      mon->state = MS_GET_BYTES;
      mon->needbits = 8;
      mon->byte = 0;
      data_callback(mon, UsbMon_DataType_PID, pid);
    } break;

    case MS_GET_BYTES: {
      uint8_t d = (uint8_t)mon->bits;
      mon->bytes[mon->byte] = d;
      mon->needbits = 8;
      if (mon->byte < MON_BYTES_SIZE) {
        mon->byte++;
      }
      data_callback(mon, UsbMon_DataType_Byte, d);
    } break;

    case MS_IDLE:
      break;

    default:
      assert(!"Unknown/undefined USB monitor state");
      break;
  }
}

// Export some internal diagnostic state for visibility in waveforms
uint32_t usb_monitor_diags(usb_monitor_ctx_t *mon) {
  // Show the PID most recently detected
  uint32_t diags = mon->lastpid;

  // Show the byte most recently received
  if (mon->byte > 0 && mon->byte <= MON_BYTES_SIZE)
    diags |= (mon->bytes[mon->byte - 1]) << 8;

  // Show the down counting of bits required
  diags |= (mon->needbits << 16);

  // Monitor state number
  diags |= mon->state << 20;

  return diags;
}
