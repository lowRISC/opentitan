// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <fstream>
#include <iostream>

#include "verilated_toplevel.h"
#include "verilator_sim_ctrl.h"

int main(int argc, char **argv) {
  prim_crc32_sim top;
  VerilatorSimCtrl &simctrl = VerilatorSimCtrl::GetInstance();
  simctrl.SetTop(&top, &top.IO_CLK, &top.IO_RST_N,
                 VerilatorSimCtrlFlags::ResetPolarityNegative);

  bool exit_app = false;
  int ret_code = simctrl.ParseCommandArgs(argc, argv, exit_app);
  if (exit_app) {
    return ret_code;
  }

  std::cout << "Simulation" << std::endl
            << "==================" << std::endl
            << std::endl;

  simctrl.RunSimulation();

  if (!simctrl.WasSimulationSuccessful()) {
    return 1;
  }

  return 0;
}
