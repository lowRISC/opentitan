// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <functional>
#include <iostream>
#include <signal.h>

#include "Vaes_tlul_shim_tb.h"
#include "sim_ctrl_extension.h"
#include "verilated_toplevel.h"
#include "verilator_sim_ctrl.h"

class AesTlulShimTb : public SimCtrlExtension {
  using SimCtrlExtension::SimCtrlExtension;

 public:
  AesTlulShimTb(aes_tlul_shim_tb *top);

  void OnClock(unsigned long sim_time);

 private:
  aes_tlul_shim_tb *top_;
};

// Constructor:
// - Set up top_ ptr
AesTlulShimTb::AesTlulShimTb(aes_tlul_shim_tb *top)
    : SimCtrlExtension{}, top_(top) {}

// Function called once every clock cycle from SimCtrl
void AesTlulShimTb::OnClock(unsigned long sim_time) {
  if (top_->test_done_o) {
    VerilatorSimCtrl::GetInstance().RequestStop(top_->test_passed_o);
  }
}

int main(int argc, char **argv) {
  int ret_code;

  // Init verilog instance
  aes_tlul_shim_tb top;

  // Init sim
  VerilatorSimCtrl &simctrl = VerilatorSimCtrl::GetInstance();
  simctrl.SetTop(&top, &top.clk_i, &top.rst_ni,
                 VerilatorSimCtrlFlags::ResetPolarityNegative);

  // Create and register VerilatorSimCtrl extension
  AesTlulShimTb aes_tlul_shim_tb(&top);
  simctrl.RegisterExtension(&aes_tlul_shim_tb);

  std::cout << "Simulation of AES TLUL Shim" << std::endl
            << "=============================" << std::endl
            << std::endl;

  // Get pass / fail from Verilator
  ret_code = simctrl.Exec(argc, argv).first;

  if (ret_code == 0) {
    std::cout << "Simulation passed!" << std::endl;
  } else {
    std::cout << "Simulation failed!" << std::endl;
  }

  return ret_code;
}
