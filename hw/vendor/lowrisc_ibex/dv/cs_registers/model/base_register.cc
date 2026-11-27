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
    // Don't panic about MCycle(H) incrementing, this is expected behavior as
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

// Returns a per-byte mask of the pmpcfg fields whose write must be ignored
// because of the Smepmp MML restriction. Smepmp v1.0 (chapter 2, item 4b),
// which newer Privileged Spec releases include in the "Machine Security
// Configuration (mseccfg) Register" section, states: "Adding a rule with
// executable privileges that either is M-mode-only or a locked Shared-Region is
// not possible and such pmpcfg writes are ignored, leaving pmpcfg unchanged."
// Setting mseccfg.RLB lifts this restriction.
//
// The check is done on the candidate value, i.e. the value each pmpcfg field
// would take after the write, not on the current register value (fields that
// are already locked are handled by GetLockMask()). With MML=1 a field with L=1
// is affected if its {X,W,R} encoding is one of (see the Smepmp truth table):
// - 0x4 (X):     M-mode-only execute-only region
// - 0x5 (X,R):   M-mode-only read/execute region
// - 0x2 (W):     locked Shared-Region, execute-only on M and S/U mode
// - 0x6 (X,W):   locked Shared-Region, read/execute on M, execute-only on S/U
// The RTL equivalent is is_mml_m_exec_cfg() in ibex_cs_registers.sv.
uint32_t PmpCfgRegister::GetMmlSuppressMask(uint32_t candidate) {
  BaseRegister *mseccfg = GetRegisterFromMap(kCSRMSeccfg);
  assert(mseccfg);
  uint32_t mseccfg_val = mseccfg->RegisterRead();
  if (!(mseccfg_val & kMSeccfgMml) || (mseccfg_val & kMSeccfgRlb))
    return 0;
  uint32_t suppress_mask = 0;
  for (int i = 0; i < 4; i++) {
    uint8_t byte_val = (candidate >> (8 * i)) & 0xFF;
    uint8_t xwr = byte_val & 0x7;
    if ((byte_val & 0x80) &&
        (xwr == 0x4 || xwr == 0x2 || xwr == 0x6 || xwr == 0x5)) {
      suppress_mask |= (0xFFu << (8 * i));
    }
  }
  return suppress_mask;
}

uint32_t PmpCfgRegister::RegisterWrite(uint32_t newval) {
  uint32_t lock_mask = GetLockMask();
  uint32_t read_value = register_value_;
  uint32_t suppress_mask = GetMmlSuppressMask(newval);

  register_value_ &= (lock_mask | suppress_mask);
  register_value_ |= (newval & ~lock_mask & ~suppress_mask);
  register_value_ = HandleReservedVals(register_value_);

  return read_value;
}

uint32_t PmpCfgRegister::RegisterSet(uint32_t newval) {
  uint32_t lock_mask = GetLockMask();
  uint32_t read_value = register_value_;
  uint32_t candidate = register_value_ | (newval & ~lock_mask);
  uint32_t suppress_mask = GetMmlSuppressMask(candidate);

  register_value_ |= (newval & ~lock_mask & ~suppress_mask);
  register_value_ = HandleReservedVals(register_value_);

  return read_value;
}

uint32_t PmpCfgRegister::RegisterClear(uint32_t newval) {
  uint32_t lock_mask = GetLockMask();
  uint32_t read_value = register_value_;
  uint32_t candidate = register_value_ & (~newval | lock_mask);
  uint32_t suppress_mask = GetMmlSuppressMask(candidate);

  register_value_ &= (~newval | lock_mask | suppress_mask);
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
  BaseRegister *mseccfg = GetRegisterFromMap(kCSRMSeccfg);
  assert(mseccfg);

  // When RLB=1, locked entries can still be modified (SMEPMP).
  if (mseccfg->RegisterRead() & kMSeccfgRlb) {
    return 0;
  }

  // Calculate which region this is
  uint32_t pmp_region = (register_address_ & 0xF);
  // Form the address of the corresponding CFG register
  uint32_t pmp_cfg_addr = 0x3A0 + (pmp_region / 4);
  // Form the address of the CFG register for the next region
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
  // Locked if own L=1, or next region is BOTH locked (L=1) and TOR mode.
  if ((cfg_value & 0x80) || ((cfg_plus1_value & 0x98) == 0x88)) {
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
