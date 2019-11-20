// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "reset_driver.h"

extern "C" void rst_register_intf(std::string name, ResetDriver *intf);
extern "C" void rst_deregister_intf(std::string name);

ResetDriver::ResetDriver(std::string name)
    : reset_delay_(1), reset_duration_(0), name_(name) {}

void ResetDriver::OnInitial(unsigned int seed) {
  generator_.seed(seed);
  // 100 to 1000 cycles between resets
  delay_dist_ = std::uniform_int_distribution<int>(100, 1000);
  rst_register_intf(name_, this);
}

void ResetDriver::OnFinal() { rst_deregister_intf(name_); }

void ResetDriver::DriveReset(unsigned char *rst_n) {
  reset_delay_--;
  if (reset_delay_ == 0) {
    reset_delay_ = delay_dist_(generator_);
    reset_duration_ = 0;
  }
  if (reset_duration_ < 3) {
    reset_duration_++;
    *rst_n = false;
  } else {
    *rst_n = true;
  }
}
