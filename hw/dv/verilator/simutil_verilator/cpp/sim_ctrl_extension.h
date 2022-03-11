// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_HW_DV_VERILATOR_SIMUTIL_VERILATOR_CPP_SIM_CTRL_EXTENSION_H_
#define OPENTITAN_HW_DV_VERILATOR_SIMUTIL_VERILATOR_CPP_SIM_CTRL_EXTENSION_H_

class SimCtrlExtension {
 public:
  virtual ~SimCtrlExtension() = default;

  /**
   * Parse command line arguments
   *
   * Process all recognized command-line arguments from argc/argv.
   * Note that other extensions might also be registered with their
   * own command line arguments.
   *
   * To make this work properly, the extension must only parse options
   * (no positional arguments) and must leave the ordering of argv
   * unchanged. In particular, if the code uses getopt_long, it should
   * pass an optstring argument starting with a '-' character.
   *
   * @param argc, argv Standard C command line arguments
   * @param exit_app Indicate that program should terminate
   * @return Return code, true == success
   */
  virtual bool ParseCLIArguments(int argc, char **argv, bool &exit_app) {
    return true;
  }

  /**
   * Function to be called prior to executing the simulation
   */
  virtual void PreExec() {}

  /**
   * Function to be called every clock cycle
   */
  virtual void OnClock(unsigned long sim_time) {}

  /**
   * Function to be called after executing the simulation
   */
  virtual void PostExec() {}
};

#endif  // OPENTITAN_HW_DV_VERILATOR_SIMUTIL_VERILATOR_CPP_SIM_CTRL_EXTENSION_H_
