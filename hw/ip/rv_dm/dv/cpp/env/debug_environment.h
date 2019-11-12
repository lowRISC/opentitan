// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef DEBUG_ENVIRONMENT_H_
#define DEBUG_ENVIRONMENT_H_

#include "env/simctrl.h"
#include "tests/dv_test.h"

#include <random>

/**
 * Class to contain all tb components
 */
class DebugEnvironment {
 public:
  DebugEnvironment();
  ~DebugEnvironment();

  /**
   * Initial setup call
   *
   * @param seed Simulation seed passed via DPI
   * @param test Name of test to load
   */
  void OnInitial(unsigned int seed, char *test);

  /**
   * Method to be called at the end of simulation
   */
  void OnFinal();

  /**
   * Method to be called on every clock cycle
   *
   * @param stop_req Simulation stop request is passed back to DPI
   */
  void GetStopReq(unsigned char *stop_req);

 private:
  SimCtrl *simctrl_;
  DVTest *dv_test_;
};

#endif  // DEBUG_ENVIRONMENT_H_
