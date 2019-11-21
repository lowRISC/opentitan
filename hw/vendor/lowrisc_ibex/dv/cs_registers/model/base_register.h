// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef BASE_REGISTER_H_
#define BASE_REGISTER_H_

#include "register_transaction.h"

#include <stdint.h>
#include <memory>
#include <vector>

/**
 * Base register class, can be specialized to add advanced functionality
 * required by different types of register
 */
class BaseRegister {
 public:
  BaseRegister(uint32_t addr,
               std::vector<std::unique_ptr<BaseRegister>> *map_pointer);
  virtual ~BaseRegister() = default;
  virtual void RegisterReset();
  virtual uint32_t RegisterWrite(uint32_t newval);
  virtual uint32_t RegisterSet(uint32_t newval);
  virtual uint32_t RegisterClear(uint32_t newval);
  virtual uint32_t RegisterRead();
  virtual bool ProcessTransaction(bool *match, RegisterTransaction *trans);
  virtual bool MatchAddr(uint32_t addr);
  virtual uint32_t GetLockMask();

 protected:
  uint32_t register_value_;
  uint32_t register_address_;
  std::vector<std::unique_ptr<BaseRegister>> *map_pointer_;
};

/**
 * PMP configuration register class
 */
class PmpCfgRegister : public BaseRegister {
  using BaseRegister::BaseRegister;

 public:
  uint32_t GetLockMask();
  uint32_t RegisterWrite(uint32_t newval);
  uint32_t RegisterSet(uint32_t newval);
  uint32_t RegisterClear(uint32_t newval);

 private:
  const uint32_t raz_mask_ = 0x9F9F9F9F;
};

/**
 * PMP address register class
 */
class PmpAddrRegister : public BaseRegister {
  using BaseRegister::BaseRegister;

 public:
  uint32_t GetLockMask();
};

/**
 * Generic class to model non-implemented (read as zero) registers
 */
class NonImpRegister : public BaseRegister {
  using BaseRegister::BaseRegister;

 public:
  uint32_t RegisterRead();
  uint32_t RegisterWrite(uint32_t newval);
  uint32_t RegisterSet(uint32_t newval);
  uint32_t RegisterClear(uint32_t newval);
};

#endif  // BASE_REGISTER_H_
