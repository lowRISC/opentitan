// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "verilated_toplevel.h"
#include "verilator_sim_ctrl.h"

int main(int argc, char **argv) {
  ibex_riscv_compliance top;
  VerilatorSimCtrl &simctrl = VerilatorSimCtrl::GetInstance();
  simctrl.SetTop(&top, &top.IO_CLK, &top.IO_RST_N,
                 VerilatorSimCtrlFlags::ResetPolarityNegative);

  simctrl.RegisterMemoryArea("ram", "TOP.ibex_riscv_compliance.u_ram");

  return simctrl.Exec(argc, argv);
}
