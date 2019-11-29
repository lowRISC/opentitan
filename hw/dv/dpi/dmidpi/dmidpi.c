// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "dmidpi.h"
#include "tcp_server.h"

#include <assert.h>
#include <pthread.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// IDCODE register
// [31:28] 0x0,    - Version
// [27:12] 0x4F54, - Part Number: "OT"
// [11:1]  0x426,  - Manufacturer Identity: Google
// [0]     0x1     - fixed
const int IDCODEVAL = 0x04F5484D;

// DTMCS register
// [31:18]  0x0  - fixed
// [17]     0x0  - dmihardreset (unused)
// [16]     0x0  - dmireset (unused)
// [15]     0x0  - fixed
// [14:12]  0x0  - RunTestIdle cycles required (0)
// [11:10]  0x0  - DMI status (unused)
// [9:4]    0x7  - Number of address bits
// [3:0]    0x1  - Protocol version (0.13)
const int DTMCSRVAL = 0x00000071;

enum jtag_state_t : uint8_t {
  TestLogicReset,
  RunTestIdle,
  SelectDrScan,
  CaptureDr,
  ShiftDr,
  Exit1Dr,
  PauseDr,
  Exit2Dr,
  UpdateDr,
  SelectIrScan,
  CaptureIr,
  ShiftIr,
  Exit1Ir,
  PauseIr,
  Exit2Ir,
  UpdateIr
};

enum jtag_reg_t : uint8_t {
  Bypass0 = 0x0,
  IdCode = 0x1,
  DTMCSR = 0x10,
  DMIAccess = 0x11,
  Bypass1 = 0x1f
};

struct jtag_ctx {
  uint32_t ir_shift_reg;
  uint64_t dr_shift_reg;
  uint32_t ir_captured;
  uint64_t dr_captured;
  uint8_t dr_length;
  uint8_t jtag_tdo;
  jtag_state_t jtag_state;
  uint8_t dmi_outstanding;
};

struct dmi_sig_values {
  uint8_t dmi_req_valid;
  uint8_t dmi_req_ready;
  uint32_t dmi_req_addr;
  uint32_t dmi_req_op;
  uint32_t dmi_req_data;
  uint8_t dmi_rsp_valid;
  uint8_t dmi_rsp_ready;
  uint32_t dmi_rsp_data;
  uint32_t dmi_rsp_resp;
  uint8_t dmi_rst_n;
};

struct dmidpi_ctx {
  struct tcp_server_ctx *sock;
  struct jtag_ctx jtag;
  struct dmi_sig_values sig;
};

/**
 * Setup the correct shift register data
 *
 * @param ctx dmidpi context object
 */
static void set_dr_data(struct dmidpi_ctx *ctx) {
  switch (ctx->jtag.ir_captured) {
    case Bypass0:
    case Bypass1:
      ctx->jtag.dr_shift_reg = 0;
      ctx->jtag.dr_length = 1;
      break;
    case IdCode:
      ctx->jtag.dr_shift_reg = IDCODEVAL;
      ctx->jtag.dr_length = 32;
      break;
    case DTMCSR:
      ctx->jtag.dr_shift_reg = DTMCSRVAL;
      ctx->jtag.dr_length = 32;
      break;
    case DMIAccess:
      ctx->jtag.dr_shift_reg = ctx->jtag.dr_captured;
      ctx->jtag.dr_length = 32 + 7 + 2;
  }
}

/**
 * Drive a new DMI transaction to the DPI interface
 *
 * @param ctx dmidpi context object
 */
static void issue_dmi_req(struct dmidpi_ctx *ctx) {
  ctx->jtag.dmi_outstanding = 1;
  ctx->sig.dmi_req_valid = 1;
  ctx->sig.dmi_req_addr = (ctx->jtag.dr_captured >> 34) & 0x7F;
  ctx->sig.dmi_req_op = ctx->jtag.dr_captured & 0x3;
  ctx->sig.dmi_req_data = (ctx->jtag.dr_captured >> 2) & 0xFFFFFFFF;
}

/**
 * Advance internal JTAG state
 *
 * @param ctx dmidpi context object
 * @param tdi tms tck JTAG signal values
 * @return true when a command completes, false otherwise
 */
static bool process_jtag_cmd(struct dmidpi_ctx *ctx, bool tdi, bool tms,
                             bool tck) {
  // Return tdo values during tck low phase
  if (!tck) {
    if (ctx->jtag.jtag_state == ShiftDr) {
      ctx->jtag.jtag_tdo = ctx->jtag.dr_shift_reg & 0x1;
    } else {
      ctx->jtag.jtag_tdo = ctx->jtag.ir_shift_reg & 0x1;
    }
    return false;
  }

  // standard JTAG state machine
  switch (ctx->jtag.jtag_state) {
    case TestLogicReset:
      // reset design
      ctx->sig.dmi_rst_n = 0;
      ctx->jtag.ir_captured = 1;
      if (!tms) {
        ctx->jtag.jtag_state = RunTestIdle;
      }
      return true;
    case RunTestIdle:
      // release reset
      ctx->sig.dmi_rst_n = 1;
      if (tms) {
        ctx->jtag.jtag_state = SelectDrScan;
      }
      return false;
    case SelectDrScan:
      if (tms) {
        ctx->jtag.jtag_state = SelectIrScan;
      } else {
        ctx->jtag.jtag_state = CaptureDr;
      }
      return false;
    case CaptureDr:
      set_dr_data(ctx);
      if (tms) {
        ctx->jtag.jtag_state = Exit1Dr;
      } else {
        ctx->jtag.jtag_state = ShiftDr;
      }
      return false;
    case ShiftDr:
      ctx->jtag.dr_shift_reg |= ((uint64_t)tdi << ctx->jtag.dr_length);
      ctx->jtag.dr_shift_reg >>= 1;
      if (tms) {
        ctx->jtag.jtag_state = Exit1Dr;
      }
      return false;
    case Exit1Dr:
      if (tms) {
        ctx->jtag.jtag_state = UpdateDr;
      } else {
        ctx->jtag.jtag_state = PauseDr;
      }
      return false;
    case PauseDr:
      if (tms) {
        ctx->jtag.jtag_state = Exit2Dr;
      }
      return false;
    case Exit2Dr:
      if (tms) {
        ctx->jtag.jtag_state = UpdateDr;
      } else {
        ctx->jtag.jtag_state = ShiftDr;
      }
      return false;
    case UpdateDr:
      ctx->jtag.dr_captured = ctx->jtag.dr_shift_reg;
      if (tms) {
        ctx->jtag.jtag_state = SelectDrScan;
      } else {
        ctx->jtag.jtag_state = RunTestIdle;
      }
      // If a DMI read or write completes, write it out
      if ((ctx->jtag.ir_captured == DMIAccess) &&
          ((ctx->jtag.dr_captured & 0x3) != 0)) {
        issue_dmi_req(ctx);
        return true;
      }
      return false;
    case SelectIrScan:
      if (tms) {
        ctx->jtag.jtag_state = TestLogicReset;
      } else {
        ctx->jtag.jtag_state = CaptureIr;
      }
      return false;
    case CaptureIr:
      ctx->jtag.ir_shift_reg = 0x5;
      if (tms) {
        ctx->jtag.jtag_state = Exit1Ir;
      } else {
        ctx->jtag.jtag_state = ShiftIr;
      }
      return false;
    case ShiftIr:
      ctx->jtag.ir_shift_reg |= ((uint32_t)tdi << 5);
      ctx->jtag.ir_shift_reg >>= 1;
      if (tms) {
        ctx->jtag.jtag_state = Exit1Ir;
      }
      return false;
    case Exit1Ir:
      if (tms) {
        ctx->jtag.jtag_state = UpdateIr;
      } else {
        ctx->jtag.jtag_state = PauseIr;
      }
      return false;
    case PauseIr:
      if (tms) {
        ctx->jtag.jtag_state = Exit2Ir;
      }
      return false;
    case Exit2Ir:
      if (tms) {
        ctx->jtag.jtag_state = UpdateIr;
      } else {
        ctx->jtag.jtag_state = ShiftIr;
      }
      return false;
    case UpdateIr:
      ctx->jtag.ir_captured = ctx->jtag.ir_shift_reg;
      if (tms) {
        ctx->jtag.jtag_state = SelectDrScan;
      } else {
        ctx->jtag.jtag_state = RunTestIdle;
      }
      return false;
  }
  return false;
}

/**
 * Process a new command byte
 *
 * @param ctx a dmi context object
 * @param cmd a packaged OpenOCD cmd
 * @return true when a command completes, false otherwise
 */
static bool process_cmd_byte(struct dmidpi_ctx *ctx, char cmd) {
  /*
   * Documentation pointer:
   * The remote_bitbang protocol implemented below is documented in the OpenOCD
   * source tree at doc/manual/jtag/drivers/remote_bitbang.txt, or online at
   * https://repo.or.cz/openocd.git/blob/HEAD:/doc/manual/jtag/drivers/remote_bitbang.txt
   */

  // parse received command byte
  if (cmd >= '0' && cmd <= '7') {
    // JTAG write
    char cmd_bit = cmd - '0';
    char tdi = (cmd_bit >> 0) & 0x1;
    char tms = (cmd_bit >> 1) & 0x1;
    char tck = (cmd_bit >> 2) & 0x1;
    return (process_jtag_cmd(ctx, tdi, tms, tck));
  } else if (cmd >= 'r' && cmd <= 'u') {
    // JTAG reset (active high from OpenOCD)
    char cmd_bit = cmd - 'r';
    char trst = ((cmd_bit >> 1) & 0x1);
    if (trst) {
      ctx->sig.dmi_rst_n = 0;
      ctx->jtag.jtag_state = RunTestIdle;
    }
    return true;
  } else if (cmd == 'R') {
    // JTAG read, send tdo as response
    char tdo_ascii = ctx->jtag.jtag_tdo + '0';
    tcp_server_write(ctx->sock, tdo_ascii);
  } else if (cmd == 'B') {
    // printf("DMI DPI: BLINK ON!\n");
  } else if (cmd == 'b') {
    // printf("DMI DPI: BLINK OFF!\n");
  } else if (cmd == 'Q') {
    // quit (client disconnect)
    printf("DMI DPI: Remote disconnected.\n");
    tcp_server_client_close(ctx->sock);
  } else {
    fprintf(stderr,
            "DMI DPI: Protocol violation detected: unsupported command %c\n",
            cmd);
    exit(1);
  }

  return false;
}

/**
 * Process DPI inputs from the design
 *
 * @param ctx dmidpi context object
 */
static void process_dmi_inputs(struct dmidpi_ctx *ctx) {
  // Deassert dmi_req_valid when acked
  if (ctx->sig.dmi_req_ready) {
    ctx->sig.dmi_req_valid = 0;
  }
  // Always ready for a resp
  ctx->sig.dmi_rsp_ready = 1;
  if (ctx->sig.dmi_rsp_valid) {
    ctx->jtag.dr_captured = (uint64_t)ctx->sig.dmi_rsp_data << 2;
    ctx->jtag.dr_captured |= (uint64_t)ctx->sig.dmi_rsp_resp & 0x3;
    // Clear req outstanding flag
    ctx->jtag.dmi_outstanding = 0;
  }
}

/**
 * Advance DMI internal state
 *
 * @param ctx dmidpi context object
 */
static void update_dmi_state(struct dmidpi_ctx *ctx) {
  assert(ctx);

  // read input from design
  process_dmi_inputs(ctx);

  // If we are waiting for a previous transaction to complete, do not attempt
  // a new one
  if (ctx->jtag.dmi_outstanding) {
    return;
  }

  char done = 0;
  while (!done) {
    // read a command byte
    char cmd;
    if (!tcp_server_read(ctx->sock, &cmd)) {
      return;
    }
    // Process command bytes until a command completes
    done = process_cmd_byte(ctx, cmd);
  }
}

void *dmidpi_create(const char *display_name, int listen_port) {
  // Create context
  struct dmidpi_ctx *ctx =
      (struct dmidpi_ctx *)calloc(1, sizeof(struct dmidpi_ctx));
  assert(ctx);

  // Set up socket details
  ctx->sock = tcp_server_create(display_name, listen_port);

  printf(
      "\n"
      "JTAG: Virtual JTAG interface %s is listening on port %d. Use\n"
      "OpenOCD and the following configuration to connect:\n"
      "  interface remote_bitbang\n"
      "  remote_bitbang_host localhost\n"
      "  remote_bitbang_port %d\n",
      display_name, listen_port, listen_port);

  return (void *)ctx;
}

void dmidpi_close(void *ctx_void) {
  struct dmidpi_ctx *ctx = (struct dmidpi_ctx *)ctx_void;
  if (!ctx) {
    return;
  }

  // Shut down the server
  tcp_server_close(ctx->sock);

  free(ctx);
}

void dmidpi_tick(void *ctx_void, svBit *dmi_req_valid,
                 const svBit dmi_req_ready, svBitVecVal *dmi_req_addr,
                 svBitVecVal *dmi_req_op, svBitVecVal *dmi_req_data,
                 const svBit dmi_rsp_valid, svBit *dmi_rsp_ready,
                 const svBitVecVal *dmi_rsp_data,
                 const svBitVecVal *dmi_rsp_resp, svBit *dmi_rst_n) {
  struct dmidpi_ctx *ctx = (struct dmidpi_ctx *)ctx_void;

  if (!ctx) {
    return;
  }

  ctx->sig.dmi_req_ready = dmi_req_ready;
  ctx->sig.dmi_rsp_valid = dmi_rsp_valid;
  ctx->sig.dmi_rsp_data = *dmi_rsp_data;
  ctx->sig.dmi_rsp_resp = *dmi_rsp_resp;

  update_dmi_state(ctx);

  *dmi_req_valid = ctx->sig.dmi_req_valid;
  *dmi_req_addr = ctx->sig.dmi_req_addr;
  *dmi_req_op = ctx->sig.dmi_req_op;
  *dmi_req_data = ctx->sig.dmi_req_data;
  *dmi_rsp_ready = ctx->sig.dmi_rsp_ready;
  *dmi_rst_n = ctx->sig.dmi_rst_n;
}
