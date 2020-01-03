// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef SIMCTRL_H_
#define SIMCTRL_H_

class SimCtrl {
 public:
  SimCtrl();
  void RequestStop(bool success);
  bool StopRequested();
  bool TestPassed();
  void OnFinal();

 private:
  bool stop_requested_;
  bool success_;
};

#endif
