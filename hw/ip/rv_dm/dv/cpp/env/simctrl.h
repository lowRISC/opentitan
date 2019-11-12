// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef SIMCTRL_H_
#define SIMCTRL_H_

class SimCtrl {
 public:
  SimCtrl();

  /**
   * TB component stop request
   *
   * Called by any TB component to request the simulation to end
   *
   * @param success Indicate pass/fail reason for stop request
   */
  void RequestStop(bool success);

  /**
   * Determine if simulation stop has been requested
   *
   * return simulation stop request status
   */
  bool StopRequested();

  /**
   * Determine if simulation test passed or failed
   *
   * return simulation pass / fail
   */
  bool TestPass();

  /**
   * Print a standard banner message for pass / fail
   */
  void PrintSimResult();

 private:
  bool stop_request_;
  bool test_success_;
};

#endif  // SIMCTRL_H_
