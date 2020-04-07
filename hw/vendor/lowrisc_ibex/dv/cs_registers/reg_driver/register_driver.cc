// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "register_driver.h"

#include <iostream>

extern "C" void reg_register_intf(std::string name, RegisterDriver *intf);
extern "C" void reg_deregister_intf(std::string name);

RegisterDriver::RegisterDriver(std::string name, RegisterModel *model,
                               SimCtrl *sc)
    : name_(name), reg_model_(model), simctrl_(sc) {}

void RegisterDriver::OnInitial(unsigned int seed) {
  transactions_driven_ = 0;
  delay_ = 1;
  reg_access_ = false;
  generator_.seed(seed);
  delay_dist_ = std::uniform_int_distribution<int>(1, 20);
  reg_register_intf(name_, this);
}

void RegisterDriver::OnFinal() {
  reg_deregister_intf(name_);
  std::cout << "[Reg driver] drove: " << transactions_driven_
            << " register transactions" << std::endl;
}

void RegisterDriver::Randomize() {
  // generate new transaction
  next_transaction_.Randomize(generator_);
  // generate new delay
  delay_ = delay_dist_(generator_);

  reg_access_ = true;
}

void RegisterDriver::CaptureTransaction(unsigned char rst_n,
                                        unsigned char illegal_csr, uint32_t op,
                                        uint32_t addr, uint32_t rdata,
                                        uint32_t wdata) {
  if (!rst_n) {
    reg_model_->RegisterReset();
  } else {
    auto trans = std::make_unique<RegisterTransaction>();
    trans->illegal_csr = illegal_csr;
    trans->csr_op = (CSRegisterOperation)op;
    trans->csr_addr = addr;
    trans->csr_rdata = rdata;
    trans->csr_wdata = wdata;
    // Ownership of trans is passed to the model
    reg_model_->NewTransaction(std::move(trans));
  }
}

void RegisterDriver::DriveOutputs(unsigned char *access, uint32_t *op,
                                  unsigned char *csr_op_en, uint32_t *addr,
                                  uint32_t *wdata) {
  *access = reg_access_;
  *csr_op_en = reg_access_;
  *op = next_transaction_.csr_op;
  *addr = next_transaction_.csr_addr;
  *wdata = next_transaction_.csr_wdata;
}

void RegisterDriver::OnClock() {
  if (transactions_driven_ >= 10000) {
    simctrl_->RequestStop(true);
  }
  if (--delay_ == 0) {
    Randomize();
    ++transactions_driven_;
  } else {
    reg_access_ = false;
  }
}
