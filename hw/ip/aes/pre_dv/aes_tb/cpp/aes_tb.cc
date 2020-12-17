// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "Vaes_sim.h"
#include "verilated_toplevel.h"
#include "verilator_sim_ctrl.h"

#include "aes_model_checker.h"
#include "aes_tlul_interface.h"

#include <functional>
#include <iostream>
#include <signal.h>

#include "sim_ctrl_extension.h"

class AESSim : public SimCtrlExtension {
  using SimCtrlExtension::SimCtrlExtension;

 public:
  AESSim(aes_sim *top);

  void OnClock(unsigned long sim_time);
  void PostExec();

 private:
  AESTLULInterface tlul_interface_;
  AESModelChecker model_checker_;
};

// Constructor:
// - Create TLULInterface + ModelChecker
AESSim::AESSim(aes_sim *top)
    : SimCtrlExtension{}, tlul_interface_(top), model_checker_(top) {}

// Function called once every clock cycle from SimCtrl
void AESSim::OnClock(unsigned long sim_time) {
  int retval = 0;

  if (sim_time > 10) {
    tlul_interface_.HandleInterface();
    retval = model_checker_.CheckModel();
  }

  if (retval) {
    VerilatorSimCtrl::GetInstance().RequestStop(false);
  } else if (!retval && tlul_interface_.StatusDone()) {
    VerilatorSimCtrl::GetInstance().RequestStop(true);
  }
}

// Function called after finishing simulation
void AESSim::PostExec() {
  std::cout << "Drove " << std::dec << tlul_interface_.GetNumTransactions()
            << " register transactions" << std::endl;
  std::cout << "Received " << std::dec << tlul_interface_.GetNumResponses()
            << " expected register responses" << std::endl;
}

int main(int argc, char **argv) {
  int ret_code;

  // Init verilog instance
  aes_sim top;

  // Init simulation
  VerilatorSimCtrl &simctrl = VerilatorSimCtrl::GetInstance();
  simctrl.SetTop(&top, &top.clk_i, &top.rst_ni,
                 VerilatorSimCtrlFlags::ResetPolarityNegative);

  // Create and register VerilatorSimCtrl extension
  AESSim aessim(&top);
  simctrl.RegisterExtension(&aessim);

  std::cout << "Simulation of AES Unit" << std::endl
            << "======================" << std::endl
            << std::endl;

  // Get pass / fail from Verilator
  ret_code = simctrl.Exec(argc, argv).first;

  return ret_code;
}
