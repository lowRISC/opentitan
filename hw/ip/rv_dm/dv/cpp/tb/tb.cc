// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "Vtb.h"
#include "verilated_toplevel.h"
#include "verilator_sim_ctrl.h"

#include <signal.h>
#include <functional>
#include <iostream>

tb *top;

VerilatorSimCtrl *simctrl;

// dummy definition since this DPI call doesn't exist
// See Ibex #317
extern "C" {
void simutil_verilator_memload(const char *file) {}
}

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

int main(int argc, char **argv) {
  // Required for plusarg calls
  Verilated::commandArgs(argc, argv);

  int retcode;
  // init top verilog instance
  top = new tb;
  // Create SimCtrl instance
  simctrl = new VerilatorSimCtrl(top, top->clk_i, top->in_rst_ni,
                                 VerilatorSimCtrlFlags::ResetPolarityNegative);

  SetupSignalHandler();

  if (!simctrl->ParseCommandArgs(argc, argv, retcode)) {
    goto free_return;
  }

  if (simctrl->TracingPossible()) {
    std::cout << "Tracing can be toggled by sending SIGUSR1 to this process:"
              << std::endl
              << "$ kill -USR1 " << getpid() << std::endl;
  }

  // Run the simulation
  simctrl->Run();

  simctrl->PrintStatistics();

  if (simctrl->TracingEverEnabled()) {
    std::cout << std::endl
              << "You can view the simulation traces by calling" << std::endl
              << "$ gtkwave " << simctrl->GetSimulationFileName() << std::endl;
  }

free_return:
  delete simctrl;
  delete top;

  return retcode;
}
