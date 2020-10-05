// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_HW_DV_DPI_USBDPI_USBDPI_H_
#define OPENTITAN_HW_DV_DPI_USBDPI_USBDPI_H_

#define TOOL_VERILATOR 1
#define TOOL_INCISIVE 0

#include <limits.h>
#include <stdio.h>
#include <svdpi.h>

// How many bits in our frame (1ms on real hardware)
#define FRAME_INTERVAL 256 * 8

// How many bits after start to assert VBUS
#define SENSE_AT 20 * 8

// Number of bytes in max output buffer line
#define MAX_OBUF 80

// Logging level (parameter to module)
#define LOG_MON 0x01  // monitor_usb (packet level)
#define LOG_BIT 0x08  // bit level

// Error insertion
#define INSERT_ERR_CRC 0
#define INSERT_ERR_PID 0
#define INSERT_ERR_BITSTUFF 0

// Index of the unimplemented endpoint to test
#define UNIMPL_EP_ID 15

#define D2P_BITS 11
#define D2P_DP 1024
#define D2P_DP_EN 512
#define D2P_DN 256
#define D2P_DN_EN 128
#define D2P_D 64
#define D2P_D_EN 32
#define D2P_SE0 16
#define D2P_SE0_EN 8
#define D2P_DPPU 4
#define D2P_DNPU 2
#define D2P_TXMODE_SE 1
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

/* Remember these go LSB first */

/* Sync is KJKJKJKK */
#define USB_SYNC 0x2a

#define USB_PID_OUT 0xE1
#define USB_PID_IN 0x69
#define USB_PID_SOF 0xA5
#define USB_PID_SETUP 0x2D
#define USB_PID_DATA0 0xC3
#define USB_PID_DATA1 0x4B
#define USB_PID_ACK 0xD2
#define USB_PID_NAK 0x5A
#define USB_PID_STALL 0x1E
#define USB_PID_NYET 0x96

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

#define SEND_MAX 32
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

struct usbdpi_ctx {
  int loglevel;
  FILE *mon_file;
  char mon_pathname[PATH_MAX];
  void *mon;
  int last_pu;
  int lastrxpid;
  int tick;
  int tick_bits;
  int recovery_time;
  int frame;
  int framepend;
  int lastframe;
  int inframe;
  int state;
  int wait;
  uint32_t driving;
  int linebits;
  int bit;
  int byte;
  int bytes;
  int datastart;
  int hostSt;
  uint8_t data[SEND_MAX];
  int baudrate_set_successfully;
};

void *usbdpi_create(const char *name, int loglevel);
void usbdpi_device_to_host(void *ctx_void, const svBitVecVal *usb_d2p);
char usbdpi_host_to_device(void *ctx_void, const svBitVecVal *usb_d2p);
void usbdpi_close(void *ctx_void);
uint32_t CRC5(uint32_t dwInput, int iBitcnt);
uint32_t CRC16(uint8_t *data, int bytes);

void *monitor_usb_init(void);
void monitor_usb(void *mon, FILE *mon_file, int log, int tick, int hdrive,
                 int p2d, int d2p, int *lastpid);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_HW_DV_DPI_USBDPI_USBDPI_H_
