// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <functional>
#include <iostream>
#include <signal.h>

#include "Vprim_ascon_duplex_tb.h"
#include "sim_ctrl_extension.h"
#include "verilated_toplevel.h"
#include "verilator_sim_ctrl.h"

class PRIMASCONDUPLEXTB : public SimCtrlExtension {
  using SimCtrlExtension::SimCtrlExtension;

 public:
  PRIMASCONDUPLEXTB(prim_ascon_duplex_tb *top);

  void OnClock(unsigned long sim_time);

 private:
  prim_ascon_duplex_tb *top_;
};

// Constructor:
// - Set up top_ ptr
PRIMASCONDUPLEXTB::PRIMASCONDUPLEXTB(prim_ascon_duplex_tb *top)
    : SimCtrlExtension{}, top_(top) {}

// Function called once every clock cycle from SimCtrl
void PRIMASCONDUPLEXTB::OnClock(unsigned long sim_time) {
  if (top_->test_done_o) {
    VerilatorSimCtrl::GetInstance().RequestStop(top_->test_passed_o);
  }
}

int main(int argc, char **argv) {
  // Init verilog instance
  prim_ascon_duplex_tb top;

  // Init sim
  VerilatorSimCtrl &simctrl = VerilatorSimCtrl::GetInstance();
  simctrl.SetTop(&top, &top.clk_i, &top.rst_ni,
                 VerilatorSimCtrlFlags::ResetPolarityNegative);

  // Create and register VerilatorSimCtrl extension
  PRIMASCONDUPLEXTB primasconduplextb(&top);
  simctrl.RegisterExtension(&primasconduplextb);

  std::cout << "Simulation of Ascon Duplex" << std::endl
            << "==========================" << std::endl
            << std::endl;

  // Get pass / fail from Verilator
  return simctrl.Exec(argc, argv).first;
}
