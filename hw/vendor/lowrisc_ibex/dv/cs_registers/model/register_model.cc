// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "register_model.h"

#include <iostream>

RegisterModel::RegisterModel(SimCtrl *sc) : simctrl_(sc) {
  // Instantiate all the registers
  for (int i = 0; i < 4; i++) {
    uint32_t reg_addr = 0x3A0 + i;
    if (PMP_ENABLE && (i < (PMP_NUM_REGIONS / 4))) {
      register_map_.push_back(
          std::make_unique<PmpCfgRegister>(reg_addr, &register_map_));
    } else {
      register_map_.push_back(
          std::make_unique<NonImpRegister>(reg_addr, &register_map_));
    }
  }
  for (int i = 0; i < 16; i++) {
    uint32_t reg_addr = 0x3B0 + i;
    if (PMP_ENABLE && (i < PMP_NUM_REGIONS)) {
      register_map_.push_back(
          std::make_unique<PmpAddrRegister>(reg_addr, &register_map_));
    } else {
      register_map_.push_back(
          std::make_unique<NonImpRegister>(reg_addr, &register_map_));
    }
  }
}

void RegisterModel::RegisterReset() {
  for (auto it = register_map_.begin(); it != register_map_.end(); ++it) {
    (*it)->RegisterReset();
  }
}

void RegisterModel::NewTransaction(std::unique_ptr<RegisterTransaction> trans) {
  // TODO add machine mode permissions to registers
  bool matched = false;
  for (auto it = register_map_.begin(); it != register_map_.end(); ++it) {
    if ((*it)->ProcessTransaction(&matched, trans.get())) {
      simctrl_->RequestStop(false);
    }
  }
  if (!matched) {
    // Non existant register
    if (!trans->illegal_csr) {
      std::cout << "Non-existant register:" << std::endl;
      trans->Print();
      std::cout << "Should have signalled an error." << std::endl;
      simctrl_->RequestStop(false);
    }
  }
}
