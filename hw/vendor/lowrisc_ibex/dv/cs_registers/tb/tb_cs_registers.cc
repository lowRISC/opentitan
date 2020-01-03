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
  int retcode = simctrl.Exec(argc, argv);
  if (!retcode) {
    // Get pass / fail from testbench
    retcode = !top.test_passed_o;
  }
  return retcode;
}
