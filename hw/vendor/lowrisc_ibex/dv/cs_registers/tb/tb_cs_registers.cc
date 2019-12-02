// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "verilated_toplevel.h"
#include "verilator_sim_ctrl.h"

// dummy definition since this DPI call doesn't exist
// TODO : remove this - see Ibex #317
extern "C" {
void simutil_verilator_memload(const char *file) {}
int simutil_verilator_set_mem(int index, const svLogicVecVal *val) { return 0; }
}

int main(int argc, char **argv) {
  tb_cs_registers top;
  VerilatorSimCtrl &simctrl = VerilatorSimCtrl::GetInstance();
  simctrl.SetTop(&top, &top.clk_i, &top.in_rst_ni,
                 VerilatorSimCtrlFlags::ResetPolarityNegative);

  return simctrl.Exec(argc, argv);
}
