// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>

#ifdef __linux__
#include <linux/limits.h>
#include <pty.h>
#elif __APPLE__
#include <util.h>
#endif

#include <assert.h>
#include <errno.h>
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <svdpi.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>

#include "spidpi.h"
#include "verilator_sim_ctrl.h"

// This holds the necessary SPI state.

struct spidpi_ctx {
  int loglevel;
  int host;
  int device;
  FILE *log_file;
  FILE *mon_file;
  void *mon;
  unsigned tick;
  uint8_t rx;
  uint8_t tx;
  bool push_tx;
};

void *spidpi_create(const char *name, int mode, int loglevel) {
  struct spidpi_ctx *ctx =
      (struct spidpi_ctx *)calloc(1, sizeof(struct spidpi_ctx));
  assert(ctx);

  ctx->loglevel = loglevel;
  ctx->tick = 0;
  ctx->rx = P2D_CSB;
  ctx->tx = 0;
  char cwd[PATH_MAX];
  char ptyname[64];
  char *cwd_rv;
  cwd_rv = getcwd(cwd, sizeof(cwd));
  assert(cwd_rv != NULL);

  int rv;
  struct termios tty;
  cfmakeraw(&tty);

  rv = openpty(&ctx->host, &ctx->device, 0, &tty, 0);
  assert(rv != -1);

  rv = ttyname_r(ctx->device, ptyname, 64);
  assert(rv == 0 && "ttyname_r failed");

  int cur_flags = fcntl(ctx->host, F_GETFL, 0);
  assert(cur_flags != -1 && "Unable to read current flags.");
  int new_flags = fcntl(ctx->host, F_SETFL, cur_flags | O_NONBLOCK);
  assert(new_flags != -1 && "Unable to set FD flags");

  // might be worth getting rid of this blahblahblah
  printf(
      "\n"
      "SPI: Created %s for %s. Connect to it with any terminal program, e.g.\n"
      "$ screen %s\n"
      "NOTE: a SPI transaction is run for every 4 characters entered.\n",
      ptyname, name, ptyname);

  char *spi_log = getenv("VERILATOR_SPI_LOG");

  // check if some logging files are requested
  if (spi_log) {
    // log SPI as ASCII-art signals (very verbose)
    char log_pathname[PATH_MAX];
    if (strchr(spi_log, 'M')) {
      // keep original name to avoid breaking some existing tool
      rv = snprintf(log_pathname, PATH_MAX, "%s/%s.log", cwd, name);
      assert(rv < PATH_MAX && rv > 0);
      ctx->mon_file = fopen(log_pathname, "wt");
      if (ctx->mon_file == NULL) {
        fprintf(stderr, "SPI: Unable to open file at %s: %s\n", log_pathname,
                strerror(errno));
        free(ctx);
        return NULL;
      }
      setlinebuf(ctx->mon_file);
      ctx->mon = monitor_spi_init(mode);
      printf(
          "SPI: Monitor output file created at %s. Works well with tail:\n"
          "$ tail -f %s\n",
          log_pathname, log_pathname);
    }

    // log SPI PTY protocol (communication with peer)
    if (strchr(spi_log, 'P')) {
      rv = snprintf(log_pathname, PATH_MAX, "%s/%s.pty.log", cwd, name);
      assert(rv < PATH_MAX && rv > 0);
      ctx->log_file = fopen(log_pathname, "wt");
      if (!ctx->log_file) {
        fprintf(stderr, "SPI: Unable to open file at %s: %s\n", log_pathname,
                strerror(errno));
        setlinebuf(ctx->log_file);
      } else {
        printf("SPI: PTY output file created at %s.\n", log_pathname);
      }
    }
  }

  ctx->push_tx = false;

  return (void *)ctx;
}

__attribute__((noinline)) uint8_t spidpi_tick2(void *ctx_void,
                                               const svLogicVecVal *d2p_data) {
  struct spidpi_ctx *ctx = (struct spidpi_ctx *)ctx_void;
  assert(ctx);

  ctx->tx = d2p_data->aval & (D2P_SDO | D2P_SDO_EN);

  if (ctx->push_tx) {
    /* add '0' in ASCII so that it easier to debug */
    uint8_t out_byte = 0x30 | ctx->tx;
    if (ctx->log_file) {
      fprintf(ctx->log_file, "@%u tx:%01x\n", ctx->tick, ctx->tx);
      fflush(ctx->log_file);
    }
    ctx->push_tx = false;
    (void)write(ctx->host, &out_byte, sizeof(out_byte));
  }

  // Will tick at the host clock
  ctx->tick++;

  if (ctx->mon && ctx->mon_file) {
    monitor_spi(ctx->mon, ctx->mon_file, ctx->loglevel, ctx->tick, ctx->rx,
                ctx->tx);
  }

  // SPI clock toggles every 4th tick (i.e. freq=primary_frequency/8)
  if (ctx->tick & 3) {
    return ctx->rx;
  }

  uint8_t in_byte;

  int n = read(ctx->host, &in_byte, sizeof(in_byte));
  if (n == -1) {
    if (errno != EAGAIN) {
      fprintf(stderr, "Read on SPI FIFO gave %s\n", strerror(errno));
    }
    return ctx->rx;
  }

  /* filter MSB so that ASCII-encoded digit can be accepted (for debug) */
  in_byte &= P2D_SCK | P2D_CSB | P2D_SDI;
  ctx->rx = in_byte;
  ctx->push_tx = true;

  if (ctx->log_file) {
    fprintf(ctx->log_file, "@%u rx:%01x\n", ctx->tick, ctx->rx);
    fflush(ctx->log_file);
  }

  return ctx->rx;
}

uint8_t spidpi_tick(void *ctx_void, const svLogicVecVal *d2p_data) {
  return spidpi_tick2(ctx_void, d2p_data);
}

void spidpi_close(void *ctx_void) {
  struct spidpi_ctx *ctx = (struct spidpi_ctx *)ctx_void;
  if (!ctx) {
    return;
  }
  if (ctx->mon_file) {
    fclose(ctx->mon_file);
  }
  if (ctx->log_file) {
    fprintf(ctx->log_file, "%u ticks\n");
    fclose(ctx->log_file);
  }
  free(ctx);
}
