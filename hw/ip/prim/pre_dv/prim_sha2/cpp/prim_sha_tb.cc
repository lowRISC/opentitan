// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <iostream>
#include <signal.h>

#include "Vprim_sha_tb.h"
#include "sim_ctrl_extension.h"
#include "verilated_toplevel.h"
#include "verilator_sim_ctrl.h"

class SHAEngineTB : public SimCtrlExtension {
 public:
  SHAEngineTB(prim_sha_tb *top);

  void OnClock(unsigned long sim_time);

 private:
  prim_sha_tb *top_;
};

// Constructor:
// - Set up top_ ptr
SHAEngineTB::SHAEngineTB(prim_sha_tb *top) : top_(top) {}

// Function called once every clock cycle from SimCtrl
void SHAEngineTB::OnClock(unsigned long sim_time) {
  if (top_->test_done_o) {
    if (top_->test_passed_o) {
      std::cout << "Test PASSED for all test vectors!" << std::endl;
    } else {
      std::cout << "Test FAILED for some test vectors." << std::endl;
    }
    VerilatorSimCtrl::GetInstance().RequestStop(true);
  }
}

int main(int argc, char **argv) {
  // Init verilog instance
  prim_sha_tb top;

  // Init sim
  VerilatorSimCtrl &simctrl = VerilatorSimCtrl::GetInstance();
  simctrl.SetTop(&top, &top.clk_i, &top.rst_ni,
                 VerilatorSimCtrlFlags::ResetPolarityNegative);

  // Create and register VerilatorSimCtrl extension
  SHAEngineTB prim_sha_tb(&top);
  simctrl.RegisterExtension(&prim_sha_tb);

  std::cout << "Simulation of SHA-2 256 Engine" << std::endl
            << "=============================" << std::endl
            << std::endl;

  // Get pass / fail from Verilator
  return simctrl.Exec(argc, argv).first;
}
