// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef VERILATOR_SIM_CTRL_H_
#define VERILATOR_SIM_CTRL_H_

#include <verilated.h>

#include <chrono>
#include <string>

#include "verilated_toplevel.h"

enum VerilatorSimCtrlFlags {
  Defaults = 0,
  ResetPolarityNegative = 1,
};

class VerilatorSimCtrl {
 public:
  VerilatorSimCtrl(VerilatedToplevel* top, CData& clk, CData& rst_n,
                   VerilatorSimCtrlFlags flags = Defaults);

  /**
   * Print help how to use this tool
   */
  void PrintHelp() const;

  /**
   * Parse command line arguments
   *
   * This removes all recognized command-line arguments from argc/argv.
   *
   * The return value of this method indicates if the program should exit with
   * retcode: if this method returns true, do *not* exit; if it returns *false*,
   * do exit.
   */
  bool ParseCommandArgs(int argc, char** argv, int& retcode);

  /**
   * Run the main loop of the simulation
   *
   * This function blocks until the simulation finishes.
   */
  void Run();

  /**
   * Initialize Rom
   */
  void InitRom(const std::string mem);

  /**
   * Initialize Ram
   */
  void InitRam(const std::string mem);

  /**
   * Initialize Flash
   */
  void InitFlash(const std::string mem);

  /**
   * Get the current time in ticks
   */
  unsigned long GetTime() { return time_; }

  /**
   * Set the number of clock cycles (periods) before the reset signal is
   * activated
   */
  void SetInitialResetDelay(unsigned int cycles);

  /**
   * Set the number of clock cycles (periods) the reset signal is activated
   */
  void SetResetDuration(unsigned int cycles);

  /**
   * Request the simulation to stop
   */
  void RequestStop();

  /**
   * Enable tracing (if possible)
   *
   * Enabling tracing can fail if no tracing support has been compiled into the
   * simulation.
   *
   * @return Is tracing enabled?
   */
  bool TraceOn();

  /**
   * Disable tracing
   *
   * @return Is tracing enabled?
   */
  bool TraceOff();

  /**
   * Is tracing currently enabled?
   */
  bool TracingEnabled() { return tracing_enabled_; }

  /**
   * Has tracing been ever enabled during the run?
   *
   * Tracing can be enabled and disabled at runtime.
   */
  bool TracingEverEnabled() { return tracing_ever_enabled_; }

  /**
   * Is tracing support compiled into the simulation?
   */
  bool TracingPossible() { return tracing_possible_; }

  /**
   * Print statistics about the simulation run
   */
  void PrintStatistics();

  const char* GetSimulationFileName() const;

 private:
  VerilatedToplevel* top_;
  CData& sig_clk_;
  CData& sig_rst_;
  VerilatorSimCtrlFlags flags_;
  unsigned long time_;
  bool init_rom_;
  bool init_ram_;
  bool init_flash_;
  std::string rom_init_file_;
  std::string ram_init_file_;
  std::string flash_init_file_;
  bool tracing_enabled_;
  bool tracing_enabled_changed_;
  bool tracing_ever_enabled_;
  bool tracing_possible_;
  unsigned int initial_reset_delay_cycles_;
  unsigned int reset_duration_cycles_;
  volatile unsigned int request_stop_;
  std::chrono::steady_clock::time_point time_begin_;
  std::chrono::steady_clock::time_point time_end_;
  VerilatedTracer tracer_;
  int term_after_cycles_;

  unsigned int GetExecutionTimeMs();
  void SetReset();
  void UnsetReset();
  bool IsFileReadable(std::string filepath);
  bool FileSize(std::string filepath, int& size_byte);
  void Trace();
};

#endif  // VERILATOR_SIM_CTRL_H_
