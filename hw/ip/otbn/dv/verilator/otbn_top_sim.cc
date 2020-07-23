// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <fstream>
#include <iomanip>
#include <iostream>
#include <svdpi.h>

#include "verilated_toplevel.h"
#include "verilator_memutil.h"
#include "verilator_sim_ctrl.h"

extern "C" {
extern unsigned int otbn_base_reg_get(int index);
}

int main(int argc, char **argv) {
  otbn_top_sim top;
  VerilatorMemUtil memutil;
  VerilatorSimCtrl &simctrl = VerilatorSimCtrl::GetInstance();
  simctrl.SetTop(&top, &top.IO_CLK, &top.IO_RST_N,
                 VerilatorSimCtrlFlags::ResetPolarityNegative);

  memutil.RegisterMemoryArea(
      "dmem", "TOP.otbn_top_sim.u_dmem.u_mem.gen_generic.u_impl_generic");
  memutil.RegisterMemoryArea(
      "imem", "TOP.otbn_top_sim.u_imem.u_mem.gen_generic.u_impl_generic");
  simctrl.RegisterExtension(&memutil);

  bool exit_app = false;
  int ret_code = simctrl.ParseCommandArgs(argc, argv, exit_app);
  if (exit_app) {
    return ret_code;
  }

  std::cout << "Simulation of OTBN" << std::endl
            << "==================" << std::endl
            << std::endl;

  simctrl.RunSimulation();

  if (!simctrl.WasSimulationSuccessful()) {
    return 1;
  }

  svSetScope(svGetScopeFromName("TOP.otbn_top_sim"));
  std::cout << "Final Register Values:" << std::endl;
  std::cout << "Reg | Value" << std::endl;
  std::cout << "----------------" << std::endl;
  for (int i = 1; i < 32; ++i) {
    std::cout << std::dec << std::setw(2) << std::setfill(' ') << i << "  | 0x"
              << std::hex << std::setw(8) << std::setfill('0')
              << otbn_base_reg_get(i) << std::endl;
  }

  return 0;
}
