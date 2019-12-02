// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef VERILATOR_SIM_CTRL_H_
#define VERILATOR_SIM_CTRL_H_

#include <chrono>
#include <functional>
#include <map>
#include <string>

#include <verilated.h>

#include "verilated_toplevel.h"

enum VerilatorSimCtrlFlags {
  Defaults = 0,
  ResetPolarityNegative = 1,
};

// Callback function to be called every clock cycle
// The parameter is simulation time
typedef std::function<void(int /* sim time */)> SimCtrlCallBack;

enum MemImageType {
  kMemImageUnknown = 0,
  kMemImageElf,
  kMemImageVmem,
};

struct MemArea {
  std::string name;      // Unique identifier
  std::string location;  // Design scope location
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
  static VerilatorSimCtrl& GetInstance();

  VerilatorSimCtrl(VerilatorSimCtrl const&) = delete;
  void operator=(VerilatorSimCtrl const&) = delete;

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
   * 1. Sets up a signal handler to enable tracing to be turned on/off during
   *    a run by sending SIGUSR1 to the process
   * 2. Parses a C-style set of command line arguments.
   * 3. Runs the simulation
   *
   * @return a main()-compatible process exit code: 0 for success, 1 in case
   *         of an error.
   */
  int Exec(int argc, char **argv);

  /**
   * A helper function to execute a standard set of run commands.
   *
   * This function performs the following tasks:
   * 1. Prints some tracer-related helper messages
   * 2. Runs the simulation
   * 3. Prints some further helper messages and statistics once the simulation
   *    has run to completion
   */
  void RunSimulation();

  /**
   * Print help how to use this tool
   */
  void PrintHelp() const;

  /**
   * Run the main loop of the simulation
   *
   * This function blocks until the simulation finishes.
   */
  void Run();

  /**
   * Register a memory as instantiated by generic ram
   *
   * The |name| must be a unique identifier. The function will return false
   * if |name| is already used. |location| is the path to the scope of the
   * instantiated memory, which needs to support the DPI-C interfaces
   * 'simutil_verilator_memload' and 'simutil_verilator_set_mem' used for
   * 'vmem' and 'elf' files, respectively.
   *
   * Memories must be registered before command arguments are parsed by
   * ParseCommandArgs() in order for them to be known.
   */
  bool RegisterMemoryArea(const std::string name, const std::string location);

  /**
   * Print a list of all registered memory regions
   *
   * @see RegisterMemoryArea()
   */
  void PrintMemRegions() const;

  /**
   * Get the current time in ticks
   */
  unsigned long GetTime() const { return time_; }

  /**
   * Get a name for this simulation
   *
   * This name is typically the name of the top-level.
   */
  std::string GetName() const;

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
   * Set a callback function to run every cycle
   */
  void SetOnClockCallback(SimCtrlCallBack callback);

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
  std::map<std::string, MemArea> mem_register_;
  int term_after_cycles_;
  SimCtrlCallBack callback_;

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
   * Parse command line arguments
   *
   * This removes all recognized command-line arguments from argc/argv.
   *
   * The return value of this method indicates if the program should exit with
   * retcode: if this method returns true, do *not* exit; if it returns *false*,
   * do exit.
   */
  bool ParseCommandArgs(int argc, char **argv, bool &exit_app);

  /**
   * Parse argument section specific to memory initialization.
   *
   * Must be in the form of: name,file[,type].
   */
  bool ParseMemArg(std::string mem_argument, std::string &name,
                   std::string &filepath, MemImageType &type);
  MemImageType DetectMemImageType(const std::string filepath);
  MemImageType GetMemImageTypeByName(const std::string name);

  unsigned int GetExecutionTimeMs() const;
  void SetReset();
  void UnsetReset();
  bool IsFileReadable(std::string filepath) const;
  bool FileSize(std::string filepath, int &size_byte) const;
  void Trace();

  /**
   * Dump an ELF file into a raw binary
   */
  bool ElfFileToBinary(const std::string &filepath, uint8_t **data,
                       size_t &len_bytes) const;

  bool MemWrite(const std::string &name, const std::string &filepath);
  bool MemWrite(const std::string &name, const std::string &filepath,
                MemImageType type);
  bool MemWrite(const MemArea &m, const std::string &filepath,
                MemImageType type);
  bool WriteElfToMem(const svScope &scope, const std::string &filepath);
  bool WriteVmemToMem(const svScope &scope, const std::string &filepath);
};

#endif  // VERILATOR_SIM_CTRL_H_
