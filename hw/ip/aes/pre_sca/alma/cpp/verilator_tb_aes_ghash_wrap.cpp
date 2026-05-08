// Copyright lowRISC contributors (OpenTitan project).
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
    tb.m_core.data_in_prev_i[i] = i;
    tb.m_core.data_out_i[i] = 4 + i;
    tb.m_core.hash_subkey_i[i] = 8 + i;
    tb.m_core.hash_subkey_i[4 + i] = 12 + i;
    tb.m_core.s_i[i] = 16 + i;
    tb.m_core.s_i[4 + i] = 20 + i;
    tb.m_core.prd_i[i] = 24 + i;
    tb.m_core.prd_i[4 + i] = 28 + i;
  }

  // Static control signals
  tb.m_core.op_i = 2;  // encrypt
  tb.m_core.num_valid_bytes_i = 16;
  tb.m_core.alert_fatal_i = 0;
  tb.m_core.out_ready_i = 0;

  // Dynamic control signals
  tb.m_core.gcm_phase_i = 1;  // GCM_INIT
  tb.m_core.in_valid_i = 0;
  tb.m_core.load_hash_subkey_i = 0;
  tb.tick();
  while (tb.m_core.in_ready_o != 1) {
    tb.tick();
  }

  // Initial clearing
  tb.m_core.clear_i = 1;
  tb.m_core.in_valid_i = 1;
  tb.tick();
  tb.m_core.clear_i = 0;
  tb.m_core.in_valid_i = 0;
  while (tb.m_core.in_ready_o != 1) {
    tb.tick();
  }

  // GCM_INIT - Load hash subkey
  tb.m_core.gcm_phase_i = 1;  // GCM_INIT
  tb.m_core.in_valid_i = 1;
  tb.m_core.load_hash_subkey_i = 1;
  tb.tick();
  tb.m_core.in_valid_i = 0;
  tb.m_core.load_hash_subkey_i = 0;
  while (tb.m_core.in_ready_o != 1) {
    tb.tick();
  }

  // GCM_INIT - Load S
  tb.m_core.gcm_phase_i = 1;  // GCM_INIT
  tb.m_core.in_valid_i = 1;
  tb.tick();
  tb.m_core.in_valid_i = 0;
  while (tb.m_core.in_ready_o != 1) {
    tb.tick();
  }

  // GCM_TEXT - Block 1
  tb.m_core.gcm_phase_i = 8;  // GCM_TEXT
  tb.m_core.in_valid_i = 1;
  tb.tick();
  tb.m_core.in_valid_i = 0;
  while (tb.m_core.in_ready_o != 1) {
    tb.tick();
  }

  // GCM_TEXT - Block 2
  tb.m_core.gcm_phase_i = 8;  // GCM_TEXT
  tb.m_core.in_valid_i = 1;
  tb.tick();
  tb.m_core.in_valid_i = 0;
  while (tb.m_core.in_ready_o != 1) {
    tb.tick();
  }

  // TAG
  tb.m_core.gcm_phase_i = 32;  // GCM_TEXT
  tb.m_core.in_valid_i = 1;
  tb.tick();
  tb.m_core.in_valid_i = 0;
  while (tb.m_core.out_valid_o != 1) {
    tb.tick();
  }
  tb.tick();

  tb.closetrace();
}
