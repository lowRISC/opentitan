// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "register_model.h"

#include <iostream>

RegisterModel::RegisterModel(SimCtrl *sc, CSRParams *params) : simctrl_(sc) {
  // Instantiate all the registers
  for (unsigned int i = 0; i < 4; i++) {
    uint32_t reg_addr = 0x3A0 + i;
    if (params->PMPEnable && (i < (params->PMPNumRegions / 4))) {
      register_map_.push_back(
          std::make_unique<PmpCfgRegister>(reg_addr, &register_map_));
    } else {
      register_map_.push_back(
          std::make_unique<NonImpRegister>(reg_addr, &register_map_));
    }
  }
  for (unsigned int i = 0; i < 16; i++) {
    uint32_t reg_addr = 0x3B0 + i;
    if (params->PMPEnable && (i < params->PMPNumRegions)) {
      register_map_.push_back(
          std::make_unique<PmpAddrRegister>(reg_addr, &register_map_));
    } else {
      register_map_.push_back(
          std::make_unique<NonImpRegister>(reg_addr, &register_map_));
    }
  }
  // mcountinhibit
  // - MSBs are always 1: unused counters cannot be enabled
  // - Bit 1 is always 0: time cannot be disabled
  uint32_t mcountinhibit_mask =
      (~((0x1 << params->MHPMCounterNum) - 1) << 3) | 0x2;
  uint32_t mcountinhibit_resval = ~((0x1 << params->MHPMCounterNum) - 1) << 3;
  register_map_.push_back(std::make_unique<WARLRegister>(
      0x320, &register_map_, mcountinhibit_mask, mcountinhibit_resval));
  // Performance counter setup
  for (unsigned int i = 3; i < 32; i++) {
    uint32_t reg_addr = 0x320 + i;
    if (i < (params->MHPMCounterNum + 3)) {
      register_map_.push_back(std::make_unique<WARLRegister>(
          reg_addr, &register_map_, 0xFFFFFFFF, 0x1 << i));
    } else {
      register_map_.push_back(
          std::make_unique<NonImpRegister>(reg_addr, &register_map_));
    }
  }
  // mcycle
  register_map_.push_back(
      std::make_unique<BaseRegister>(0xB00, &register_map_));
  // minstret
  register_map_.push_back(
      std::make_unique<BaseRegister>(0xB02, &register_map_));
  // Generate masks from counter width parameter
  uint32_t mhpmcounter_mask_low, mhpmcounter_mask_high;
  if (params->MHPMCounterWidth >= 64) {
    mhpmcounter_mask_low = 0x0;
    mhpmcounter_mask_high = 0x0;
  } else {
    uint64_t mask = ~((0x1L << params->MHPMCounterWidth) - 1);
    mhpmcounter_mask_low = mask & 0xFFFFFFFF;
    mhpmcounter_mask_high = mask >> 32;
  }
  // Performance counter low word
  for (unsigned int i = 3; i < 32; i++) {
    uint32_t reg_addr = 0xB00 + i;
    if (i < (params->MHPMCounterNum + 3)) {
      register_map_.push_back(std::make_unique<WARLRegister>(
          reg_addr, &register_map_, mhpmcounter_mask_low, 0));
    } else {
      register_map_.push_back(
          std::make_unique<NonImpRegister>(reg_addr, &register_map_));
    }
  }
  // mcycleh
  register_map_.push_back(
      std::make_unique<BaseRegister>(0xB80, &register_map_));
  // minstreth
  register_map_.push_back(
      std::make_unique<BaseRegister>(0xB82, &register_map_));
  // Performance counter high word
  for (unsigned int i = 3; i < 32; i++) {
    uint32_t reg_addr = 0xB80 + i;
    if (i < (params->MHPMCounterNum + 3)) {
      register_map_.push_back(std::make_unique<WARLRegister>(
          reg_addr, &register_map_, mhpmcounter_mask_high, 0));
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
