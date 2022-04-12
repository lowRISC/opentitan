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
  virtual bool MatchAddr(uint32_t addr, uint32_t addr_mask = 0xFFFFFFFF);
  virtual uint32_t GetLockMask();

 protected:
  uint32_t register_value_;
  uint32_t register_address_;
  std::vector<std::unique_ptr<BaseRegister>> *map_pointer_;
  BaseRegister *GetRegisterFromMap(uint32_t addr);
};

/**
 * Machine Security Configuration class
 *
 * Has special behaviour for when bits are locked so requires a custom
 * `GetLockMask` implementation
 */
class MSeccfgRegister : public BaseRegister {
 public:
  MSeccfgRegister(uint32_t addr,
                  std::vector<std::unique_ptr<BaseRegister>> *map_pointer);
  uint32_t GetLockMask();

 private:
  bool AnyPmpCfgsLocked();
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
  uint32_t HandleReservedVals(uint32_t cfg_val);
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

/**
 * Generic class of WARL registers
 */
class WARLRegister : public BaseRegister {
  using BaseRegister::BaseRegister;

 protected:
  uint32_t register_mask_;
  uint32_t register_value_reset_;

 public:
  WARLRegister(uint32_t addr,
               std::vector<std::unique_ptr<BaseRegister>> *map_pointer,
               uint32_t mask, uint32_t resval);
  uint32_t GetLockMask();
  void RegisterReset();
};

#endif  // BASE_REGISTER_H_
