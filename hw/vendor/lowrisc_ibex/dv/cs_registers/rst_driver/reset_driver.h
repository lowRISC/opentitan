// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef RESET_DRIVER_H_
#define RESET_DRIVER_H_

#include <random>
#include <string>

/**
 * Class to randomize and drive reset signals
 */
class ResetDriver {
 public:
  ResetDriver(std::string name);
  void OnInitial(unsigned int seed);
  void OnFinal();
  void DriveReset(unsigned char *rst_n);

 private:
  int reset_delay_;
  int reset_duration_;
  std::string name_;
  std::default_random_engine generator_;
  std::uniform_int_distribution<int> delay_dist_;
};

#endif  // RESET_DRIVER_H_
