// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <functional>
#include <iostream>
#include <signal.h>

#include "Vaes_cipher_core_tb.h"
#include "sim_ctrl_extension.h"
#include "verilated_toplevel.h"
#include "verilator_sim_ctrl.h"

class AESCipherCoreTB : public SimCtrlExtension {
  using SimCtrlExtension::SimCtrlExtension;

 public:
  AESCipherCoreTB(aes_cipher_core_tb *top);

  void OnClock(unsigned long sim_time);

 private:
  aes_cipher_core_tb *top_;
};

// Constructor:
// - Set up top_ ptr
AESCipherCoreTB::AESCipherCoreTB(aes_cipher_core_tb *top)
    : SimCtrlExtension{}, top_(top) {}

// Function called once every clock cycle from SimCtrl
void AESCipherCoreTB::OnClock(unsigned long sim_time) {
  if (top_->test_done_o) {
    VerilatorSimCtrl::GetInstance().RequestStop(top_->test_passed_o);
  }
}

int main(int argc, char **argv) {
  int ret_code;

  // Init verilog instance
  aes_cipher_core_tb top;

  // Init sim
  VerilatorSimCtrl &simctrl = VerilatorSimCtrl::GetInstance();
  simctrl.SetTop(&top, &top.clk_i, &top.rst_ni,
                 VerilatorSimCtrlFlags::ResetPolarityNegative);

  // Create and register VerilatorSimCtrl extension
  AESCipherCoreTB aes_cipher_core_tb(&top);
  simctrl.RegisterExtension(&aes_cipher_core_tb);

  std::cout << "Simulation of AES Cipher Core" << std::endl
            << "=============================" << std::endl
            << std::endl;

  // Get pass / fail from Verilator
  ret_code = simctrl.Exec(argc, argv).first;

  return ret_code;
}
