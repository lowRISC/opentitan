// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <functional>
#include <iostream>
#include <signal.h>

#include "Vkmac_reduced_tb.h"
#include "sim_ctrl_extension.h"
#include "verilated_toplevel.h"
#include "verilator_sim_ctrl.h"

class KMACReducedTB : public SimCtrlExtension {
  using SimCtrlExtension::SimCtrlExtension;

 public:
  KMACReducedTB(kmac_reduced_tb *top);

  void OnClock(unsigned long sim_time);

 private:
  kmac_reduced_tb *top_;
};

// Constructor:
// - Set up top_ ptr
KMACReducedTB::KMACReducedTB(kmac_reduced_tb *top)
    : SimCtrlExtension{}, top_(top) {}

// Function called once every clock cycle from SimCtrl
void KMACReducedTB::OnClock(unsigned long sim_time) {
  if (top_->test_done_o) {
    VerilatorSimCtrl::GetInstance().RequestStop(top_->test_passed_o);
  }
}

int main(int argc, char **argv) {
  int ret_code;

  // Init verilog instance
  kmac_reduced_tb top;

  // Init sim
  VerilatorSimCtrl &simctrl = VerilatorSimCtrl::GetInstance();
  simctrl.SetTop(&top, &top.clk_i, &top.rst_ni,
                 VerilatorSimCtrlFlags::ResetPolarityNegative);

  // Create and register VerilatorSimCtrl extension
  KMACReducedTB kmac_reduced_tb(&top);
  simctrl.RegisterExtension(&kmac_reduced_tb);

  std::cout << "Simulation of KMAC Reduced" << std::endl
            << "==========================" << std::endl
            << std::endl;

  // Get pass / fail from Verilator
  ret_code = simctrl.Exec(argc, argv).first;

  return ret_code;
}
