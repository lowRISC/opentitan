// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <signal.h>

#include <iostream>

#include "Vtop_earlgrey_verilator.h"
#include "verilated_toplevel.h"
#include "verilator_sim_ctrl.h"

VERILATED_TOPLEVEL(top_earlgrey_verilator)

top_earlgrey_verilator *top;
VerilatorSimCtrl *simctrl;

static void SignalHandler(int sig) {
  if (!simctrl) {
    return;
  }

  switch (sig) {
    case SIGINT:
      simctrl->RequestStop();
      break;
    case SIGUSR1:
      if (simctrl->TracingEnabled()) {
        simctrl->TraceOff();
      } else {
        simctrl->TraceOn();
      }
      break;
  }
}

static void SetupSignalHandler() {
  struct sigaction sigIntHandler;

  sigIntHandler.sa_handler = SignalHandler;
  sigemptyset(&sigIntHandler.sa_mask);
  sigIntHandler.sa_flags = 0;

  sigaction(SIGINT, &sigIntHandler, NULL);
  sigaction(SIGUSR1, &sigIntHandler, NULL);
}

/**
 * Get the current simulation time
 *
 * Called by $time in Verilog, converts to double, to match what SystemC does
 */
double sc_time_stamp() { return simctrl->GetTime(); }

int main(int argc, char **argv) {
  int retcode;
  top = new top_earlgrey_verilator;
  simctrl = new VerilatorSimCtrl(top, top->clk_i, top->rst_ni,
                                 VerilatorSimCtrlFlags::ResetPolarityNegative);

  SetupSignalHandler();

  if (!simctrl->ParseCommandArgs(argc, argv, retcode)) {
    goto free_return;
  }

  std::cout << "Simulation of OpenTitan Earl Grey" << std::endl
            << "=================================" << std::endl
            << std::endl;

  if (simctrl->TracingPossible()) {
    std::cout << "Tracing can be toggled by sending SIGUSR1 to this process:"
              << std::endl
              << "$ kill -USR1 " << getpid() << std::endl;
  }

  // Initialize ROM
  simctrl->InitRom(
      "TOP.top_earlgrey_verilator.top_earlgrey.u_rom_rom"
      ".gen_mem_generic.u_impl_generic");

  // Initialize Ram
  simctrl->InitRam(
      "TOP.top_earlgrey_verilator.top_earlgrey.u_ram1p_ram_main"
      ".gen_mem_generic.u_impl_generic");

  // Initialize Flash
  //  simctrl->InitFlash(
  //      "TOP.top_earlgrey_verilator.top_earlgrey.u_flash_eflash.gen_flash."
  //      "u_impl_generic.gen_flash_banks[0].u_impl_generic.gen_mem_generic.u_impl_"
  //      "generic");
  simctrl->InitFlash(
      "TOP.top_earlgrey_verilator.top_earlgrey.u_flash_eflash."
      "gen_flash_banks[0].u_flash.gen_flash.u_impl_generic.u_mem.gen_mem_"
      "generic.u_impl_"
      "generic");

  simctrl->Run();
  simctrl->PrintStatistics();

  if (simctrl->TracingEverEnabled()) {
    std::cout << std::endl
              << "You can view the simulation traces by calling" << std::endl
              << "$ gtkwave " << simctrl->GetSimulationFileName() << std::endl;
  }

free_return:
  delete top;
  delete simctrl;
  return retcode;
}
