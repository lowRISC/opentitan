// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "Vtb_cs_registers.h"
#include "verilated_toplevel.h"
#include "verilator_sim_ctrl.h"

tb_cs_registers *top;
VerilatorSimCtrl *simctrl;

// dummy definition since this DPI call doesn't exist
// TODO : remove this - see Ibex #317
extern "C" {
void simutil_verilator_memload(const char *file) {}
}

int main(int argc, char **argv) {
  int retcode = 0;
  // init top verilog instance
  top = new tb_cs_registers;
  // Create SimCtrl instance
  simctrl = new VerilatorSimCtrl(top, top->clk_i, top->in_rst_ni,
                                 VerilatorSimCtrlFlags::ResetPolarityNegative);

  // Setup the simulation
  retcode = simctrl->SetupSimulation(argc, argv);

  // Run the simulation
  simctrl->RunSimulation();

  delete top;
  delete simctrl;
  return retcode;
}
