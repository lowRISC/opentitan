// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_HW_DV_VERILATOR_SIMUTIL_VERILATOR_CPP_VERILATOR_SIM_CTRL_H_
#define OPENTITAN_HW_DV_VERILATOR_SIMUTIL_VERILATOR_CPP_VERILATOR_SIM_CTRL_H_

#include <chrono>
#include <string>
#include <vector>

#include "sim_ctrl_extension.h"
#include "verilated_toplevel.h"

enum VerilatorSimCtrlFlags {
  Defaults = 0,
  ResetPolarityNegative = 1,
};

/**
 * Simulation controller for verilated simulations
 */
class VerilatorSimCtrl {
 public:
  /**
   * Get the simulation controller instance
   *
   * @see SetTop()
   */
  static VerilatorSimCtrl &GetInstance();

  VerilatorSimCtrl(VerilatorSimCtrl const &) = delete;
  void operator=(VerilatorSimCtrl const &) = delete;

  /**
   * Set the top-level design
   */
  void SetTop(VerilatedToplevel *top, CData *sig_clk, CData *sig_rst,
              VerilatorSimCtrlFlags flags = Defaults);

  /**
   * Setup and run the simulation (all in one)
   *
   * Use this function as high-level entry point, suitable for most use cases.
   *
   * SetTop() must be called before this function.
   *
   * This function performs the following tasks:
   * 1. Parses a C-style set of command line arguments (see ParseCommandArgs())
   * 2. Runs the simulation (see RunSimulation())
   *
   * @return a main()-compatible process exit code: 0 for success, 1 in case
   *         of an error.
   */
  int Exec(int argc, char **argv);

  /**
   * Parse command line arguments
   *
   * Process all recognized command-line arguments from argc/argv.
   *
   * @param argc, argv Standard C command line arguments
   * @param exit_app Indicate that program should terminate
   * @return Return code, true == success
   */
  bool ParseCommandArgs(int argc, char **argv, bool &exit_app);

  /**
   * A helper function to execute a standard set of run commands.
   *
   * This function performs the following tasks:
   * 1. Sets up a signal handler to enable tracing to be turned on/off during
   *    a run by sending SIGUSR1 to the process
   * 2. Prints some tracer-related helper messages
   * 3. Runs the simulation
   * 4. Prints some further helper messages and statistics once the simulation
   *    has run to completion
   */
  void RunSimulation();

  /**
   * Get the simulation result
   */
  bool WasSimulationSuccessful() const { return simulation_success_; }

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
  void RequestStop(bool simulation_success);

  /**
   * Register an extension to be called automatically
   */
  void RegisterExtension(SimCtrlExtension *ext);

  /**
   * Get the current time in ticks
   */
  unsigned long GetTime() const { return time_; }

 private:
  VerilatedToplevel *top_;
  CData *sig_clk_;
  CData *sig_rst_;
  VerilatorSimCtrlFlags flags_;
  unsigned long time_;
  bool tracing_enabled_;
  bool tracing_enabled_changed_;
  bool tracing_ever_enabled_;
  bool tracing_possible_;
  unsigned int initial_reset_delay_cycles_;
  unsigned int reset_duration_cycles_;
  volatile unsigned int request_stop_;
  volatile bool simulation_success_;
  std::chrono::steady_clock::time_point time_begin_;
  std::chrono::steady_clock::time_point time_end_;
  VerilatedTracer tracer_;
  int term_after_cycles_;
  std::vector<SimCtrlExtension *> extension_array_;

  /**
   * Default constructor
   *
   * Use GetInstance() instead.
   */
  VerilatorSimCtrl();

  /**
   * Register the signal handler
   */
  void RegisterSignalHandler();

  /**
   * Signal handler callback
   *
   * Use RegisterSignalHandler() to setup.
   */
  static void SignalHandler(int sig);

  /**
   * Print help how to use this tool
   */
  void PrintHelp() const;

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
  bool TracingEnabled() const { return tracing_enabled_; }

  /**
   * Has tracing been ever enabled during the run?
   *
   * Tracing can be enabled and disabled at runtime.
   */
  bool TracingEverEnabled() const { return tracing_ever_enabled_; }

  /**
   * Is tracing support compiled into the simulation?
   */
  bool TracingPossible() const { return tracing_possible_; }

  /**
   * Print statistics about the simulation run
   */
  void PrintStatistics() const;

  /**
   * Get the file name of the trace file
   */
  const char *GetTraceFileName() const;

  /**
   * Run the main loop of the simulation
   *
   * This function blocks until the simulation finishes.
   */
  void Run();

  /**
   * Get a name for this simulation
   *
   * This name is typically the name of the top-level.
   */
  std::string GetName() const;

  /**
   * Get the wallclock execution time in ms
   */
  unsigned int GetExecutionTimeMs() const;

  /**
   * Assert the reset signal
   */
  void SetReset();

  /**
   * Deassert the reset signal
   */
  void UnsetReset();

  /**
   * Return the size of a file
   */
  bool FileSize(std::string filepath, int &size_byte) const;

  /**
   * Perform tracing in Verilator if required
   */
  void Trace();
};

#endif  // OPENTITAN_HW_DV_VERILATOR_SIMUTIL_VERILATOR_CPP_VERILATOR_SIM_CTRL_H_
