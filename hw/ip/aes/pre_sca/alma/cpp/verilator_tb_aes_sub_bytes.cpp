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
  for (int i = 0; i < 4; ++i) {
    tb.m_core.data_i[i] = i;
    tb.m_core.mask_i[i] = 4 + i;
    tb.m_core.prd_i[i] = 8 + i;
  }

  // Control signals
  tb.m_core.out_ack_i = 3;  // SP2V_HIGH, always ack
  tb.m_core.op_i = 0;       // encrypt

  tb.m_core.en_i = 4;      // SP2V_LOW, disable
  tb.m_core.prd_we_i = 1;  // Present new PRD in next cycle.
  tb.tick();
  tb.m_core.en_i = 3;      // SP2V_HIGH, enable
  tb.m_core.prd_we_i = 0;  // Keep previous PRD.
  tb.tick();

  while (tb.m_core.out_req_o != 3) {
    tb.tick();
  }
  tb.tick();

  tb.closetrace();
}
