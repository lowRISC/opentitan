// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "base_register.h"

#include <cassert>
#include <iostream>

BaseRegister::BaseRegister(
    uint32_t addr, std::vector<std::unique_ptr<BaseRegister>> *map_pointer)
    : register_value_(0), register_address_(addr), map_pointer_(map_pointer) {}

uint32_t BaseRegister::RegisterWrite(uint32_t newval) {
  uint32_t lock_mask = GetLockMask();
  uint32_t read_value = register_value_;
  register_value_ &= lock_mask;
  register_value_ |= (newval & ~lock_mask);
  return read_value;
}

uint32_t BaseRegister::RegisterSet(uint32_t newval) {
  uint32_t lock_mask = GetLockMask();
  uint32_t read_value = register_value_;
  register_value_ |= (newval & ~lock_mask);
  return read_value;
}

uint32_t BaseRegister::RegisterClear(uint32_t newval) {
  uint32_t lock_mask = GetLockMask();
  uint32_t read_value = register_value_;
  register_value_ &= (~newval | lock_mask);
  return read_value;
}

bool BaseRegister::MatchAddr(uint32_t addr, uint32_t addr_mask) {
  return ((addr & addr_mask) == (register_address_ & addr_mask));
}

bool BaseRegister::ProcessTransaction(bool *match, RegisterTransaction *trans) {
  uint32_t read_val;
  if (!MatchAddr(trans->csr_addr)) {
    return false;
  }
  *match = true;
  switch (trans->csr_op) {
    case kCSRRead:
      read_val = RegisterRead();
      break;
    case kCSRWrite:
      read_val = RegisterWrite(trans->csr_wdata);
      break;
    case kCSRSet:
      read_val = RegisterSet(trans->csr_wdata);
      break;
    case kCSRClear:
      read_val = RegisterClear(trans->csr_wdata);
      break;
  }
  if (trans->csr_addr == kCSRMCycle || trans->csr_addr == kCSRMCycleH) {
    // MCycle(H) can increment or even overflow without TB interaction
    if (trans->csr_rdata < read_val) {
      std::cout << "MCycle(H) overflow detected" << std::endl;
    }
    // else if (read_val != trans->csr_rdata) {
    //  std::cout << "MCycle(H) incrementing as expected" << std::endl;
    //}
    // Don't panic about MCycle(H) incremeting, this is expected behavior as
    // the clock is always running. Silently ignore mismatches for MCycle(H).
  } else if (read_val != trans->csr_rdata) {
    std::cout << "Error, transaction:" << std::endl;
    trans->Print();
    std::cout << "Expected rdata: " << std::hex << read_val << std::dec
              << std::endl;
    return true;
  }
  return false;
}

void BaseRegister::RegisterReset() { register_value_ = 0; }

uint32_t BaseRegister::RegisterRead() { return register_value_; }

uint32_t BaseRegister::GetLockMask() { return 0; }

BaseRegister *BaseRegister::GetRegisterFromMap(uint32_t addr) {
  for (auto &reg : *map_pointer_) {
    if (reg->MatchAddr(addr)) {
      return reg.get();
    }
  }

  return nullptr;
}

MSeccfgRegister::MSeccfgRegister(
    uint32_t addr, std::vector<std::unique_ptr<BaseRegister>> *map_pointer)
    : BaseRegister(addr, map_pointer) {}

bool MSeccfgRegister::AnyPmpCfgsLocked() {
  for (auto &reg : *map_pointer_) {
    // Iterate through PMPCfgX CSRs, returning true is any has a lock bit set
    if (reg->MatchAddr(kCSRPMPCfg0, 0xfffffffc)) {
      if ((reg->RegisterRead() & 0x80808080) != 0) {
        return true;
      }
    }
  }

  return false;
}

uint32_t MSeccfgRegister::GetLockMask() {
  uint32_t lock_mask = 0xFFFFFFF8;

  // When RLB == 0 and any PMPCfgX has a lock bit set RLB must remain 0
  if (AnyPmpCfgsLocked() && ((register_value_ & kMSeccfgRlb) == 0)) {
    lock_mask |= kMSeccfgRlb;
  }

  // Once set MMWP cannot be unset
  if (register_value_ & kMSeccfgMmwp) {
    lock_mask |= kMSeccfgMmwp;
  }

  // Once set MML cannot be unset
  if (register_value_ & kMSeccfgMml) {
    lock_mask |= kMSeccfgMml;
  }

  return lock_mask;
}

uint32_t PmpCfgRegister::GetLockMask() {
  BaseRegister *mseccfg = GetRegisterFromMap(kCSRMSeccfg);
  assert(mseccfg);

  if (mseccfg->RegisterRead() & kMSeccfgRlb) {
    return 0;
  }

  uint32_t lock_mask = 0;
  if (register_value_ & 0x80)
    lock_mask |= 0xFF;
  if (register_value_ & 0x8000)
    lock_mask |= 0xFF00;
  if (register_value_ & 0x800000)
    lock_mask |= 0xFF0000;
  if (register_value_ & 0x80000000)
    lock_mask |= 0xFF000000;
  return lock_mask;
}

uint32_t PmpCfgRegister::RegisterWrite(uint32_t newval) {
  uint32_t lock_mask = GetLockMask();
  uint32_t read_value = register_value_;

  register_value_ &= lock_mask;
  register_value_ |= (newval & ~lock_mask);
  register_value_ = HandleReservedVals(register_value_);

  return read_value;
}

uint32_t PmpCfgRegister::RegisterSet(uint32_t newval) {
  uint32_t lock_mask = GetLockMask();
  uint32_t read_value = register_value_;

  register_value_ |= (newval & ~lock_mask);
  register_value_ = HandleReservedVals(register_value_);

  return read_value;
}

uint32_t PmpCfgRegister::RegisterClear(uint32_t newval) {
  uint32_t lock_mask = GetLockMask();
  uint32_t read_value = register_value_;

  register_value_ &= (~newval | lock_mask);
  register_value_ = HandleReservedVals(register_value_);

  return read_value;
}

uint32_t PmpCfgRegister::HandleReservedVals(uint32_t cfg_val) {
  BaseRegister *mseccfg = GetRegisterFromMap(kCSRMSeccfg);
  assert(mseccfg);

  cfg_val &= raz_mask_;

  if (mseccfg->RegisterRead() & kMSeccfgMml) {
    // No reserved L/R/W/X values when MML Set
    return cfg_val;
  }

  for (int i = 0; i < 4; i++) {
    // Reserved check, W = 1, R = 0
    if (((cfg_val >> (8 * i)) & 0x3) == 0x2) {
      cfg_val &= ~(0x3 << (8 * i));
    }
  }

  return cfg_val;
}

uint32_t PmpAddrRegister::GetLockMask() {
  // Calculate which region this is
  uint32_t pmp_region = (register_address_ & 0xF);
  // Form the address of the corresponding CFG register
  uint32_t pmp_cfg_addr = 0x3A0 + (pmp_region / 4);
  // Form the address of the CFG registerfor the next region
  // For region 15, this will point to a non-existant register, which is fine
  uint32_t pmp_cfg_plus1_addr = 0x3A0 + ((pmp_region + 1) / 4);
  uint32_t cfg_value = 0;
  uint32_t cfg_plus1_value = 0;
  // Find and read the two CFG registers
  for (auto it = map_pointer_->begin(); it != map_pointer_->end(); ++it) {
    if ((*it)->MatchAddr(pmp_cfg_addr)) {
      cfg_value = (*it)->RegisterRead();
    }
    if ((*it)->MatchAddr(pmp_cfg_plus1_addr)) {
      cfg_plus1_value = (*it)->RegisterRead();
    }
  }
  // Shift to the relevant bits in the CFG registers
  cfg_value >>= ((pmp_region & 0x3) * 8);
  cfg_plus1_value >>= (((pmp_region + 1) & 0x3) * 8);
  // Locked if the lock bit is set, or the next region is TOR
  if ((cfg_value & 0x80) || ((cfg_plus1_value & 0x18) == 0x8)) {
    return 0xFFFFFFFF;
  } else {
    return 0;
  }
}

uint32_t NonImpRegister::RegisterRead() { return 0; }

uint32_t NonImpRegister::RegisterWrite(uint32_t newval) { return 0; }

uint32_t NonImpRegister::RegisterSet(uint32_t newval) { return 0; }

uint32_t NonImpRegister::RegisterClear(uint32_t newval) { return 0; }

WARLRegister::WARLRegister(
    uint32_t addr, std::vector<std::unique_ptr<BaseRegister>> *map_pointer,
    uint32_t mask, uint32_t resval)
    : BaseRegister{addr, map_pointer},
      register_mask_(mask),
      register_value_reset_(resval) {}

void WARLRegister::RegisterReset() { register_value_ = register_value_reset_; }

uint32_t WARLRegister::GetLockMask() { return register_mask_; }
