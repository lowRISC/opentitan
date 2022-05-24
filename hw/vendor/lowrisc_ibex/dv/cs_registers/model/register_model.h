// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef REGISTER_MODEL_H_
#define REGISTER_MODEL_H_

#include <stdint.h>
#include <memory>
#include <vector>

#include "base_register.h"
#include "register_transaction.h"
#include "register_types.h"
#include "simctrl.h"

/**
 * Class modelling CS register state and checking against RTL
 */
class RegisterModel {
 public:
  RegisterModel(SimCtrl *sc, CSRParams *params);

  void NewTransaction(std::unique_ptr<RegisterTransaction> trans);
  void RegisterReset();

 private:
  std::vector<std::unique_ptr<BaseRegister>> register_map_;
  SimCtrl *simctrl_;
};

#endif  // REGISTER_MODEL_H_
