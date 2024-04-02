// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <functional>
#include <iostream>
#include <signal.h>

#include "Vascon_p_tb.h"
#include "sim_ctrl_extension.h"
#include "verilated_toplevel.h"
#include "verilator_sim_ctrl.h"

class ASCONPTB : public SimCtrlExtension {
  using SimCtrlExtension::SimCtrlExtension;

 public:
  ASCONPTB(ascon_p_tb *top);

  void OnClock(unsigned long sim_time);

 private:
  ascon_p_tb *top_;
};

// Constructor:
// - Set up top_ ptr
ASCONPTB::ASCONPTB(ascon_p_tb *top) : SimCtrlExtension{}, top_(top) {}

// Function called once every clock cycle from SimCtrl
void ASCONPTB::OnClock(unsigned long sim_time) {
  if (top_->test_done_o) {
    VerilatorSimCtrl::GetInstance().RequestStop(top_->test_passed_o);
  }
}

int main(int argc, char **argv) {
  // Init verilog instance
  ascon_p_tb top;

  // Init sim
  VerilatorSimCtrl &simctrl = VerilatorSimCtrl::GetInstance();
  simctrl.SetTop(&top, &top.clk_i, &top.rst_ni,
                 VerilatorSimCtrlFlags::ResetPolarityNegative);

  // Create and register VerilatorSimCtrl extension
  ASCONPTB asconptb(&top);
  simctrl.RegisterExtension(&asconptb);

  std::cout << "Simulation of Ascon Permutation" << std::endl
            << "===============================" << std::endl
            << std::endl;

  // Get pass / fail from Verilator
  return simctrl.Exec(argc, argv).first;
}
