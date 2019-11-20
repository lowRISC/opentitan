// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef REGISTER_ENVIRONMENT_H_
#define REGISTER_ENVIRONMENT_H_

#include "register_driver.h"
#include "register_model.h"
#include "reset_driver.h"
#include "simctrl.h"

/**
 * Class to instantiate all tb components
 */
class RegisterEnvironment {
 public:
  RegisterEnvironment();

  void OnInitial(unsigned int seed);
  void OnFinal();

  void GetStopReq(unsigned char *stop_req);

 private:
  SimCtrl *simctrl_;
  RegisterModel *reg_model_;
  RegisterDriver *reg_driver_;
  ResetDriver *rst_driver_;
};

#endif  // REGISTER_ENVIRONMENT_H_
