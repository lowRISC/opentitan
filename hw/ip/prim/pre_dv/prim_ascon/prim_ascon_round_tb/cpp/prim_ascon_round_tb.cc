// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <functional>
#include <iostream>
#include <signal.h>

#include "Vprim_ascon_round_tb.h"
#include "sim_ctrl_extension.h"
#include "verilated_toplevel.h"
#include "verilator_sim_ctrl.h"

class PRIMASCONROUNDTB : public SimCtrlExtension {
  using SimCtrlExtension::SimCtrlExtension;

 public:
  PRIMASCONROUNDTB(prim_ascon_round_tb *top);

  void OnClock(unsigned long sim_time);

 private:
  prim_ascon_round_tb *top_;
};

// Constructor:
// - Set up top_ ptr
PRIMASCONROUNDTB::PRIMASCONROUNDTB(prim_ascon_round_tb *top)
    : SimCtrlExtension{}, top_(top) {}

// Function called once every clock cycle from SimCtrl
void PRIMASCONROUNDTB::OnClock(unsigned long sim_time) {
  if (top_->test_done_o) {
    VerilatorSimCtrl::GetInstance().RequestStop(top_->test_passed_o);
  }
}

int main(int argc, char **argv) {
  // Init verilog instance
  prim_ascon_round_tb top;

  // Init sim
  VerilatorSimCtrl &simctrl = VerilatorSimCtrl::GetInstance();
  simctrl.SetTop(&top, &top.clk_i, &top.rst_ni,
                 VerilatorSimCtrlFlags::ResetPolarityNegative);

  // Create and register VerilatorSimCtrl extension
  PRIMASCONROUNDTB primasconroundtb(&top);
  simctrl.RegisterExtension(&primasconroundtb);

  std::cout << "Simulation of Ascon Round" << std::endl
            << "=========================" << std::endl
            << std::endl;

  // Get pass / fail from Verilator
  return simctrl.Exec(argc, argv).first;
}
