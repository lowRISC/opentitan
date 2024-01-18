// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <iostream>
#include <signal.h>

#include "Vprim_sha_multimode32_tb.h"
#include "sim_ctrl_extension.h"
#include "verilated_toplevel.h"
#include "verilator_sim_ctrl.h"

class SHAMultiMode32TB : public SimCtrlExtension {
 public:
  SHAMultiMode32TB(prim_sha_multimode32_tb *top);

  void OnClock(unsigned long sim_time);

 private:
  prim_sha_multimode32_tb *top_;
};

// Constructor:
// - Set up top_ ptr
SHAMultiMode32TB::SHAMultiMode32TB(prim_sha_multimode32_tb *top) : top_(top) {}

// Function called once every clock cycle from SimCtrl
void SHAMultiMode32TB::OnClock(unsigned long sim_time) {
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
  prim_sha_multimode32_tb top;

  // Init sim
  VerilatorSimCtrl &simctrl = VerilatorSimCtrl::GetInstance();
  simctrl.SetTop(&top, &top.clk_i, &top.rst_ni,
                 VerilatorSimCtrlFlags::ResetPolarityNegative);

  // Create and register VerilatorSimCtrl extension
  SHAMultiMode32TB prim_sha_multimode32_tb(&top);
  simctrl.RegisterExtension(&prim_sha_multimode32_tb);

  std::cout << "Simulation of SHA-2 32-bit Multi-Mode Engine" << std::endl
            << "=============================" << std::endl
            << std::endl;

  // Get pass / fail from Verilator
  return simctrl.Exec(argc, argv).first;
}
