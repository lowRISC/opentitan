// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <signal.h>

#include <iostream>
#include <memory>
#include <fstream>

#include "ibex_pcounts.h"
#include "verilated_toplevel.h"
#include "verilator_sim_ctrl.h"

std::shared_ptr<VerilatorSimCtrl> simctrl(nullptr);

int main(int argc, char **argv) {
  int retcode;

  auto top = std::make_shared<ibex_simple_system>();

  simctrl = std::make_shared<VerilatorSimCtrl>(
      top.get(), top->IO_CLK, top->IO_RST_N,
      VerilatorSimCtrlFlags::ResetPolarityNegative);

  retcode = simctrl->SetupSimulation(argc, argv);

  if (retcode != 0)
    return retcode;

  // Initialize RAM
  simctrl->InitRam("TOP.ibex_simple_system.u_ram");

  std::cout << "Simulation of Ibex" << std::endl
            << "==================" << std::endl
            << std::endl;

  simctrl->RunSimulation();

  std::cout << "\nPerformance Counters" << std::endl
            << "====================" << std::endl;
  std::cout << ibex_pcount_string(
      top->ibex_simple_system__DOT__mhpmcounter_vals, false);

  std::ofstream pcount_csv("ibex_simple_system_pcount.csv");
  pcount_csv << ibex_pcount_string(
      top->ibex_simple_system__DOT__mhpmcounter_vals, true);

  return 0;
}
