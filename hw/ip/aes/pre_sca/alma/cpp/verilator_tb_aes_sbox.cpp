// Copyright lowRISC contributors.
// Copyright IAIK.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdio.h>

#include "Vcircuit.h"
#include "testbench.h"

int main(int argc, char **argv) {
  Verilated::commandArgs(argc, argv);
  Testbench<Vcircuit> tb;
  tb.opentrace("tmp.vcd");

  tb.reset();

  // Data signals - we don't really care about the data fed to the module.
  // The whole tracing is really just about control signals.
  tb.m_core.data_i = 0x12;
  tb.m_core.mask_i = 0x34;
  tb.m_core.prd_i = 0x56789AB;

  // Control signals
  tb.m_core.op_i = 0;  // encrypt
  tb.m_core.out_ack_i = 0;

  tb.m_core.en_i = 0;
  tb.m_core.prd_we_i = 1;  // Present new PRD in next cycle.
  tb.tick();
  tb.m_core.en_i = 1;
  tb.m_core.prd_we_i = 1;  // Keep previous PRD.
  tb.tick();

  while (tb.m_core.out_req_o != 1) {
    tb.tick();
  }
  tb.tick();

  tb.closetrace();
}
