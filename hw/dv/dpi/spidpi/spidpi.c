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
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>

#include "spidpi.h"
#include "verilator_sim_ctrl.h"

// Enable this define to stop tracing at cycle 4
// and resume at the first SPI packet
// #define CONTROL_TRACE

void *spidpi_create(const char *name, int mode, int loglevel) {
  int i;
  struct spidpi_ctx *ctx =
      (struct spidpi_ctx *)calloc(1, sizeof(struct spidpi_ctx));
  assert(ctx);

  ctx->loglevel = loglevel;
  ctx->mon = monitor_spi_init(mode);
  ctx->tick = 0;
  ctx->msbfirst = 1;
  ctx->nmax = MAX_TRANSACTION;
  ctx->nin = 0;
  ctx->nout = 0;
  ctx->bout = 0;
  ctx->state = SP_IDLE;
  /* mode is CPOL << 1 | CPHA
   * cpol = 0 --> external clock matches internal
   * cpha = 0 --> drive on internal falling edge, capture on rising
   */
  ctx->cpol = ((mode == 0) || (mode == 2)) ? 0 : 1;
  ctx->cpha = ((mode == 1) || (mode == 3)) ? 1 : 0;
  /* CPOL = 1 for clock idle high */
  ctx->driving = P2D_CSB | ((ctx->cpol) ? P2D_SCK : 0);
  char cwd[PATH_MAX];
  char *cwd_rv;
  cwd_rv = getcwd(cwd, sizeof(cwd));
  assert(cwd_rv != NULL);

  int rv;
  struct termios tty;
  cfmakeraw(&tty);

  rv = openpty(&ctx->host, &ctx->device, 0, &tty, 0);
  assert(rv != -1);

  rv = ttyname_r(ctx->device, ctx->ptyname, 64);
  assert(rv == 0 && "ttyname_r failed");

  int cur_flags = fcntl(ctx->host, F_GETFL, 0);
  assert(cur_flags != -1 && "Unable to read current flags.");
  int new_flags = fcntl(ctx->host, F_SETFL, cur_flags | O_NONBLOCK);
  assert(new_flags != -1 && "Unable to set FD flags");

  printf(
      "\n"
      "SPI: Created %s for %s. Connect to it with any terminal program, e.g.\n"
      "$ screen %s\n"
      "NOTE: a SPI transaction is run for every 4 characters entered.\n",
      ctx->ptyname, name, ctx->ptyname);

  rv = snprintf(ctx->mon_pathname, PATH_MAX, "%s/%s.log", cwd, name);
  assert(rv <= PATH_MAX && rv > 0);
  ctx->mon_file = fopen(ctx->mon_pathname, "w");
  if (ctx->mon_file == NULL) {
    fprintf(stderr, "SPI: Unable to open file at %s: %s\n", ctx->mon_pathname,
            strerror(errno));
    return NULL;
  }
  // more useful for tail -f
  setlinebuf(ctx->mon_file);
  printf(
      "SPI: Monitor output file created at %s. Works well with tail:\n"
      "$ tail -f %s\n",
      ctx->mon_pathname, ctx->mon_pathname);

  return (void *)ctx;
}

char spidpi_tick(void *ctx_void, const svLogicVecVal *d2p_data) {
  struct spidpi_ctx *ctx = (struct spidpi_ctx *)ctx_void;
  assert(ctx);
  int d2p = d2p_data->aval;

  // Will tick at the host clock
  ctx->tick++;

#ifdef CONTROL_TRACE
  if (ctx->tick == 4) {
    VerilatorSimCtrl::GetInstance().TraceOff();
  }
#endif

  monitor_spi(ctx->mon, ctx->mon_file, ctx->loglevel, ctx->tick, ctx->driving,
              d2p);

  if (ctx->state == SP_IDLE) {
    int n = read(ctx->host, &(ctx->buf[ctx->nin]), ctx->nmax - ctx->nin);
    if (n == -1) {
      if (errno != EAGAIN) {
        fprintf(stderr, "Read on SPI FIFO gave %s\n", strerror(errno));
      }
    } else {
      ctx->nin += n;
      if (ctx->nin == ctx->nmax) {
        ctx->nout = 0;
        ctx->nin = 0;
        ctx->bout = ctx->msbfirst ? 0x80 : 0x01;
        ctx->bin = ctx->msbfirst ? 0x80 : 0x01;
        ctx->din = 0;
        ctx->state = SP_CSFALL;
#ifdef CONTROL_TRACE
        VerilatorSimCtrl::GetInstance().TraceOn();
#endif
      }
    }
  }
  // SPI clock toggles every 4th tick (i.e. freq=primary_frequency/8)
  if ((ctx->tick & 3) || (ctx->state == SP_IDLE)) {
    return ctx->driving;
  }

  // Only get here on sck edges when active
  int internal_sck = (ctx->tick & 4) ? 1 : 0;
  int set_sck = (internal_sck ? P2D_SCK : 0);
  if (ctx->cpol) {
    set_sck ^= P2D_SCK;
  }

  if (internal_sck == ctx->cpha) {
    // host driving edge (falling for mode 0)
    switch (ctx->state) {
      case SP_DMOVE:
        // SCLK low, CSB low
        ctx->driving =
            set_sck | (ctx->buf[ctx->nout] & ctx->bout) ? P2D_SDI : 0;
        ctx->bout = (ctx->msbfirst) ? ctx->bout >> 1 : ctx->bout << 1;
        if ((ctx->bout & 0xff) == 0) {
          ctx->bout = ctx->msbfirst ? 0x80 : 0x01;
          ctx->nout++;
          if (ctx->nout == ctx->nmax) {
            ctx->state = SP_LASTBIT;
          }
        }
        break;
      case SP_LASTBIT:
        ctx->state = SP_CSRISE;
        // fallthrough
      default:
        ctx->driving = set_sck | (ctx->driving & ~P2D_SCK);
        break;
    }
  } else {
    // host other edge (rising for mode 0)
    switch (ctx->state) {
        // Read input data (opposite edge to sending)
        // both DMOVE and LASTBIT states are data moving ones!
      case SP_DMOVE:
      case SP_LASTBIT:
        ctx->din = ctx->din | ((d2p & D2P_SDO) ? ctx->bin : 0);
        ctx->bin = (ctx->msbfirst) ? ctx->bin >> 1 : ctx->bin << 1;
        if (ctx->bin == 0) {
          int rv = write(ctx->host, &(ctx->din), 1);
          assert(rv == 1 && "write() failed.");
          ctx->bin = (ctx->msbfirst) ? 0x80 : 0x01;
          ctx->din = 0;
        }
        ctx->driving = set_sck | (ctx->driving & ~P2D_SCK);
        break;
      case SP_CSFALL:
        // CSB low, drive SDI to first bit
        ctx->driving =
            (set_sck | (ctx->buf[ctx->nout] & ctx->bout) ? P2D_SDI : 0);
        ctx->state = SP_DMOVE;
        break;
      case SP_CSRISE:
        // CSB high, clock stopped
        ctx->driving = P2D_CSB;
        ctx->state = SP_IDLE;
        break;
      case SP_FINISH:
        VerilatorSimCtrl::GetInstance().RequestStop(true);
        break;
      default:
        ctx->driving = set_sck | (ctx->driving & ~P2D_SCK);
        break;
    }
  }
  return ctx->driving;
}

void spidpi_close(void *ctx_void) {
  struct spidpi_ctx *ctx = (struct spidpi_ctx *)ctx_void;
  if (!ctx) {
    return;
  }
  fclose(ctx->mon_file);
  free(ctx);
}
