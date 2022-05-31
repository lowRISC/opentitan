// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "verilated_toplevel.h"
#include "verilator_sim_ctrl.h"

int main(int argc, char **argv) {
  tb_cs_registers top;
  VerilatorSimCtrl &simctrl = VerilatorSimCtrl::GetInstance();
  simctrl.SetTop(&top, &top.clk_i, &top.in_rst_ni,
                 VerilatorSimCtrlFlags::ResetPolarityNegative);


  // Get pass / fail from Verilator
  auto pr = simctrl.Exec(argc, argv);
  int ret_code = pr.first;
  bool ran_simulation = pr.second;

  if (ret_code != 0 || !ran_simulation) {
    return ret_code;
  }

  // Get pass / fail from testbench
  return !top.test_passed_o;
}
