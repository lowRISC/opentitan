// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef REGISTER_DRIVER_H_
#define REGISTER_DRIVER_H_

#include "register_model.h"
#include "register_transaction.h"
#include "simctrl.h"

#include <random>
#include <string>

/**
 * Class to randomize and drive CS register reads/writes
 */
class RegisterDriver {
 public:
  RegisterDriver(std::string name, RegisterModel *model, SimCtrl *sc);

  void OnInitial(unsigned int seed);
  void OnClock();
  void OnFinal();

  void CaptureTransaction(unsigned char rst_n, unsigned char illegal_csr,
                          uint32_t op, uint32_t addr, uint32_t rdata,
                          uint32_t wdata);
  void DriveOutputs(unsigned char *access, uint32_t *op, unsigned char *op_en,
                    uint32_t *addr, uint32_t *wdata);

 private:
  void Randomize();

  std::default_random_engine generator_;
  int delay_;
  bool reg_access_;
  CSRegisterOperation reg_op_;
  std::uniform_int_distribution<int> delay_dist_;
  uint32_t reg_addr_;
  uint32_t reg_wdata_;
  int transactions_driven_;
  RegisterTransaction next_transaction_;

  std::string name_;
  RegisterModel *reg_model_;
  SimCtrl *simctrl_;
};

#endif  // REGISTER_DRIVER_H_
