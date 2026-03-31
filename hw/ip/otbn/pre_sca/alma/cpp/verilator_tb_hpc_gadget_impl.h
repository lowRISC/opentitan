// Copyright lowRISC contributors (OpenTitan project).
// Copyright IAIK.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_HW_IP_OTBN_PRE_SCA_ALMA_CPP_VERILATOR_TB_HPC_GADGET_IMPL_H_
#define OPENTITAN_HW_IP_OTBN_PRE_SCA_ALMA_CPP_VERILATOR_TB_HPC_GADGET_IMPL_H_

// Shared testbench implementation for HPC gadget Alma verification.
// Include this file after defining HPC_RAND_MASK.

#define HPC_SHARE0 0x2
#define HPC_SHARE1 0x3

#include <random>
#include <stdio.h>

#include "Vcircuit.h"
#include "testbench.h"

int main(int argc, char **argv) {
  Verilated::commandArgs(argc, argv);
  Testbench<Vcircuit> tb;
  tb.opentrace("tmp.vcd");

  std::random_device rd;
  std::mt19937 gen(rd());
  std::uniform_int_distribution<uint32_t> dis(0, 0xFFFFFFFF);

  tb.reset();

  tb.m_core.rand_i = dis(gen) & HPC_RAND_MASK;
  tb.m_core.share0_i = HPC_SHARE0;
  tb.m_core.share1_i = HPC_SHARE1;
  tb.m_core.en_i = 0x0;
  tb.tick();

  tb.m_core.en_i = 0x1;
  for (int i = 0; i < 7; i++) {
    tb.tick();
    tb.m_core.en_i = 0x0;
  }

  tb.closetrace();
  return 0;
}

#endif  // OPENTITAN_HW_IP_OTBN_PRE_SCA_ALMA_CPP_VERILATOR_TB_HPC_GADGET_IMPL_H_
