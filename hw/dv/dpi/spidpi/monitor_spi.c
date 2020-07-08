// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#include "spidpi.h"

#define MON_BUFLEN 65

struct mon_ctx {
  int cpol;
  int cpha;
  int msbfirst;
  uint32_t prev_p2d;
  uint32_t prev_d2p;
  int bpos;
  int poff;

  unsigned char mobuf[MON_BUFLEN];
  unsigned char sobuf[MON_BUFLEN];
};

void *monitor_spi_init(int mode) {
  struct mon_ctx *mon = (struct mon_ctx *)calloc(1, sizeof(struct mon_ctx));
  assert(mon);

  /* mode is CPOL << 1 | CPHA
   * cpol = 0 --> external clock matches internal
   * cpha = 0 --> drive on internal falling edge, capture on rising
   */
  mon->cpol = (mode & 2) >> 1;
  mon->cpha = mode & 1;
  mon->prev_p2d = 0;
  mon->prev_d2p = 0;
  mon->msbfirst = 1;

  return (void *)mon;
}

/*
 * Simple drawing of a waveform vertically (line by line)
 *
 * Use an array to hold the three character string to be printed
 * based on old value/enable and new value/enable
 *
 * The strings are made positioning | \ and /
 * made less readable because \ has to be escaped as \\
 * The array of strings is indexed by a value formed by 4 bits
 * new value, new enable, old value, old enable
 *
 * Array index can be constructed from these bit defines:
 */
#define BST_OLD_EN 0x1
#define BST_OLD 0x2
#define BST_NEW_EN 0x4
#define BST_NEW 0x8

const char *vert[16] = {
    " | ",   // old disabled, new disabled
    "\\  ",  // old 0, new disabled
    " | ",   // old disabled, new disabled
    "  /",   // old 1, new disabled
    "/  ",   // old disabled, new 0
    "|  ",   // old 0, new 0
    "/  ",   // old disabled, new 0
    " / ",   // old 1, new 0
    " | ",   // old disabled, new disabled
    "\\  ",  // old 0, new disabled
    " | ",   // old disabled, new disabled
    "  /",   // old 1, new disabled
    "  \\",  // old disabled, new 1
    " \\ ",  // old 0, new 1
    "  \\",  // old disabled, new 1
    "  |"    // old 1, new 1
};

/**
 * Get three characters representing change in bit
 *
 * @param cur - bit vector that includes new value of bit and enable
 * @param old - bit vector that includes old value of bit and enable
 * @param mask - one-hot that indicates bit position of signal in new/old
 * @param enmask - one-hot that indicates bit position of enable in new/old
 * set enmask to zero if signal is always enabled
 *
 * @return three character string representing signal waveform
 */
const char *vertical_bit(int cur, int old, int mask, int enmask) {
  int cur_en, old_en;
  if (enmask) {
    // enmask is a mask indicating the bit position in cur/old of enable
    cur_en = (cur & enmask) ? BST_NEW_EN : 0;
    old_en = (old & enmask) ? BST_OLD_EN : 0;
  } else {
    // signal is always enabled
    cur_en = BST_NEW_EN;
    old_en = BST_OLD_EN;
  }
  cur = (cur & mask) ? BST_NEW : 0;
  old = (old & mask) ? BST_OLD : 0;
  return vert[cur | old | cur_en | old_en];
}

static void log_signals(struct mon_ctx *mon, FILE *mon_file, int tick, int p2d,
                        int d2p) {
  fprintf(mon_file, "%8d SPI: ", tick);
  fprintf(mon_file, "%s  ", vertical_bit(p2d, mon->prev_p2d, P2D_CSB, 0));
  fprintf(mon_file, "%s  ", vertical_bit(p2d, mon->prev_p2d, P2D_SCK, 0));
  fprintf(mon_file, "%s  ", vertical_bit(p2d, mon->prev_p2d, P2D_SDI, 0));
  fprintf(mon_file, "%s  ",
          vertical_bit(d2p, mon->prev_d2p, D2P_SDO, D2P_SDO_EN));
}

static void log_packet(struct mon_ctx *mon, FILE *mon_file) {
  fprintf(mon_file, "H>D: ");
  for (int i = 0; i < mon->poff; i++) {
    fprintf(mon_file, "%02x ", mon->mobuf[i]);
  }
  fprintf(mon_file, "D>H: ");
  for (int i = 0; i < mon->poff; i++) {
    fprintf(mon_file, "%02x ", mon->sobuf[i]);
  }
  fprintf(mon_file, "\n");
}

static void capture_bit(struct mon_ctx *mon, FILE *mon_file, int p2d, int d2p) {
  if (((mon->cpol == mon->cpha) && (p2d & P2D_SCK)) ||
      ((mon->cpol != mon->cpha) && !(p2d & P2D_SCK))) {
    uint32_t new_mobit = (p2d & P2D_SDI) ? mon->bpos : 0;
    uint32_t new_sobit = (d2p & D2P_SDO) ? mon->bpos : 0;
    // check for setup time
    if ((p2d & P2D_SDI) != (mon->prev_p2d & P2D_SDI)) {
      fprintf(mon_file, "Check SDI tSU ");
    }
    if ((d2p & D2P_SDO) != (mon->prev_d2p & D2P_SDO)) {
      fprintf(mon_file, "Check SDO tSU ");
    }
    mon->mobuf[mon->poff] |= new_mobit;
    mon->sobuf[mon->poff] |= new_sobit;
    mon->bpos = (mon->msbfirst) ? (mon->bpos >> 1) : ((mon->bpos << 1) & 0xff);
    if (mon->bpos == 0) {
      mon->bpos = (mon->msbfirst) ? 0x80 : 0x1;
      if (mon->poff < (MON_BUFLEN - 1)) {
        mon->poff++;
      }
      // clear because it will be ORed into
      mon->mobuf[mon->poff] = 0;
      mon->sobuf[mon->poff] = 0;
    }
  }
}
/**
 * SPI device monitor
 *
 * @param mon_void - monitor context structure
 * @param mon_file - FILE * for output to be written
 * @param loglevel - details to log
 * @param tick - simulation time
 * @param p2d - bits of signals from pins to device
 * @param d2p - bits of signals from device to pins
 */

void monitor_spi(void *mon_void, FILE *mon_file, int loglevel, int tick,
                 int p2d, int d2p) {
  struct mon_ctx *mon = (struct mon_ctx *)mon_void;
  assert(mon);
  int logbits = (loglevel & 0x1);
  int logpkts = (loglevel & 0x8);

  if ((tick == 1) && logbits) {
    fprintf(mon_file, "              CSB SCK MO  MI\n");
  }
  if ((p2d == mon->prev_p2d) && (d2p == mon->prev_d2p) && (p2d & P2D_CSB)) {
    return;
  }

  if (logbits) {
    log_signals(mon, mon_file, tick, p2d, d2p);
  }

  if (!logpkts) {
    fprintf(mon_file, "\n");
    mon->prev_p2d = p2d;
    mon->prev_d2p = d2p;
    return;
  }
  if ((p2d & P2D_CSB) && !(mon->prev_p2d & P2D_CSB)) {
    // end of packet
    log_packet(mon, mon_file);
    mon->poff = 0;
  } else {
    if (!(p2d & P2D_CSB) && (mon->prev_p2d & P2D_CSB)) {
      // start of packet
      mon->poff = 0;
      // clear because it will be ORed into
      mon->mobuf[0] = 0;
      mon->sobuf[0] = 0;
      mon->bpos = (mon->msbfirst) ? 0x80 : 0x1;
    } else if (!(p2d & P2D_CSB) && !(mon->prev_p2d & P2D_CSB)) {
      // inside packet
      if ((p2d & P2D_SCK) != (mon->prev_p2d & P2D_SCK)) {
        // found a clock edge, check if it is one to capture on
        capture_bit(mon, mon_file, p2d, d2p);
      }
    }
    if (logbits) {
      fprintf(mon_file, "\n");
    }
  }
  mon->prev_p2d = p2d;
  mon->prev_d2p = d2p;
}
