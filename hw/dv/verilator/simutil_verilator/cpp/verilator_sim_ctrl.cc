// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "verilator_sim_ctrl.h"

#include <getopt.h>
#include <iostream>
#include <signal.h>
#include <sys/stat.h>
#include <verilated.h>

// This is defined by Verilator and passed through the command line
#ifndef VM_TRACE
#define VM_TRACE 0
#endif

/**
 * Get the current simulation time
 *
 * Called by $time in Verilog, converts to double, to match what SystemC does
 */
double sc_time_stamp() { return VerilatorSimCtrl::GetInstance().GetTime(); }

#ifdef VL_USER_STOP
/**
 * A simulation stop was requested, e.g. through $stop() or $error()
 *
 * This function overrides Verilator's default implementation to more gracefully
 * shut down the simulation.
 */
void vl_stop(const char *filename, int linenum, const char *hier) VL_MT_UNSAFE {
  VerilatorSimCtrl::GetInstance().RequestStop(false);
}
#endif

VerilatorSimCtrl &VerilatorSimCtrl::GetInstance() {
  static VerilatorSimCtrl instance;
  return instance;
}

void VerilatorSimCtrl::SetTop(VerilatedToplevel *top, CData *sig_clk,
                              CData *sig_rst, VerilatorSimCtrlFlags flags) {
  top_ = top;
  sig_clk_ = sig_clk;
  sig_rst_ = sig_rst;
  flags_ = flags;
}

std::pair<int, bool> VerilatorSimCtrl::Exec(int argc, char **argv) {
  bool exit_app = false;
  bool good_cmdline = ParseCommandArgs(argc, argv, exit_app);
  if (exit_app) {
    return std::make_pair(good_cmdline ? 0 : 1, false);
  }

  RunSimulation();

  int retcode = WasSimulationSuccessful() ? 0 : 1;
  return std::make_pair(retcode, true);
}

static bool read_ul_arg(unsigned long *arg_val, const char *arg_name,
                        const char *arg_text) {
  assert(arg_val && arg_name && arg_text);

  bool bad_fmt = false;
  bool out_of_range = false;

  // We have a stricter input format that strtoul: no leading space and no
  // leading plus or minus signs (strtoul has magic behaviour if the input
  // starts with a minus sign, but we don't want that). We're using auto base
  // detection, but a valid number will always start with 0-9 (since hex
  // constants start with "0x")
  if (!(('0' <= arg_text[0]) && (arg_text[0] <= '9'))) {
    bad_fmt = true;
  } else {
    char *txt_end;
    *arg_val = strtoul(arg_text, &txt_end, 0);

    // If txt_end doesn't point at a \0 then we didn't read the entire
    // argument.
    if (*txt_end) {
      bad_fmt = true;
    } else {
      // If the value was too big to fit in an unsigned long, strtoul sets
      // errno to ERANGE.
      if (errno != 0) {
        assert(errno == ERANGE);
        out_of_range = true;
      }
    }
  }

  if (bad_fmt) {
    std::cerr << "ERROR: Bad format for " << arg_name << " argument: `"
              << arg_text << "' is not an unsigned integer.\n";
    return false;
  }
  if (out_of_range) {
    std::cerr << "ERROR: Bad format for " << arg_name << " argument: `"
              << arg_text << "' is too big.\n";
    return false;
  }

  return true;
}

bool VerilatorSimCtrl::ParseCommandArgs(int argc, char **argv, bool &exit_app) {
  const struct option long_options[] = {
      {"term-after-cycles", required_argument, nullptr, 'c'},
      {"trace", no_argument, nullptr, 't'},
      {"help", no_argument, nullptr, 'h'},
      {nullptr, no_argument, nullptr, 0}};

  while (1) {
    int c = getopt_long(argc, argv, ":c:th", long_options, nullptr);
    if (c == -1) {
      break;
    }

    // Disable error reporting by getopt
    opterr = 0;

    switch (c) {
      case 0:
        break;
      case 't':
        if (!tracing_possible_) {
          std::cerr << "ERROR: Tracing has not been enabled at compile time."
                    << std::endl;
          exit_app = true;
          return false;
        }
        TraceOn();
        break;
      case 'c':
        if (!read_ul_arg(&term_after_cycles_, "term-after-cycles", optarg)) {
          exit_app = true;
          return false;
        }
        break;
      case 'h':
        PrintHelp();
        exit_app = true;
        break;
      case ':':  // missing argument
        std::cerr << "ERROR: Missing argument." << std::endl << std::endl;
        exit_app = true;
        return false;
      case '?':
      default:;
        // Ignore unrecognized options since they might be consumed by
        // Verilator's built-in parsing below.
    }
  }

  // Pass args to verilator
  Verilated::commandArgs(argc, argv);

  // Parse arguments for all registered extensions
  for (auto it = extension_array_.begin(); it != extension_array_.end(); ++it) {
    if (!(*it)->ParseCLIArguments(argc, argv, exit_app)) {
      exit_app = true;
      return false;
      if (exit_app) {
        return true;
      }
    }
  }
  return true;
}

void VerilatorSimCtrl::RunSimulation() {
  RegisterSignalHandler();

  // Print helper message for tracing
  if (TracingPossible()) {
    std::cout << "Tracing can be toggled by sending SIGUSR1 to this process:"
              << std::endl
              << "$ kill -USR1 " << getpid() << std::endl;
  }
  // Call all extension pre-exec methods
  for (auto it = extension_array_.begin(); it != extension_array_.end(); ++it) {
    (*it)->PreExec();
  }
  // Run the simulation
  Run();
  // Call all extension post-exec methods
  for (auto it = extension_array_.begin(); it != extension_array_.end(); ++it) {
    (*it)->PostExec();
  }
  // Print simulation speed info
  PrintStatistics();
  // Print helper message for tracing
  if (TracingEverEnabled()) {
    std::cout << std::endl
              << "You can view the simulation traces by calling" << std::endl
              << "$ gtkwave " << GetTraceFileName() << std::endl;
  }
}

void VerilatorSimCtrl::SetInitialResetDelay(unsigned int cycles) {
  initial_reset_delay_cycles_ = cycles;
}

void VerilatorSimCtrl::SetResetDuration(unsigned int cycles) {
  reset_duration_cycles_ = cycles;
}

void VerilatorSimCtrl::SetTimeout(unsigned int cycles) {
  term_after_cycles_ = cycles;
}

void VerilatorSimCtrl::RequestStop(bool simulation_success) {
  request_stop_ = true;
  simulation_success_ &= simulation_success;
}

void VerilatorSimCtrl::RegisterExtension(SimCtrlExtension *ext) {
  extension_array_.push_back(ext);
}

VerilatorSimCtrl::VerilatorSimCtrl()
    : top_(nullptr),
      time_(0),
      tracing_enabled_(false),
      tracing_enabled_changed_(false),
      tracing_ever_enabled_(false),
      tracing_possible_(VM_TRACE),
      initial_reset_delay_cycles_(2),
      reset_duration_cycles_(2),
      request_stop_(false),
      simulation_success_(true),
      tracer_(VerilatedTracer()),
      term_after_cycles_(0) {}

void VerilatorSimCtrl::RegisterSignalHandler() {
  struct sigaction sigIntHandler;

  sigIntHandler.sa_handler = SignalHandler;
  sigemptyset(&sigIntHandler.sa_mask);
  sigIntHandler.sa_flags = 0;

  sigaction(SIGINT, &sigIntHandler, NULL);
  sigaction(SIGUSR1, &sigIntHandler, NULL);
}

void VerilatorSimCtrl::SignalHandler(int sig) {
  VerilatorSimCtrl &simctrl = VerilatorSimCtrl::GetInstance();

  switch (sig) {
    case SIGINT:
      simctrl.RequestStop(true);
      break;
    case SIGUSR1:
      if (simctrl.TracingEnabled()) {
        simctrl.TraceOff();
      } else {
        simctrl.TraceOn();
      }
      break;
  }
}

void VerilatorSimCtrl::PrintHelp() const {
  std::cout << "Execute a simulation model for " << GetName() << "\n\n";
  if (tracing_possible_) {
    std::cout << "-t|--trace\n"
                 "  Write a trace file from the start\n\n";
  }
  std::cout << "-c|--term-after-cycles=N\n"
               "  Terminate simulation after N cycles. 0 means no timeout.\n\n"
               "-h|--help\n"
               "  Show help\n\n"
               "All arguments are passed to the design and can be used "
               "in the design, e.g. by DPI modules.\n\n";
}

bool VerilatorSimCtrl::TraceOn() {
  bool old_tracing_enabled = tracing_enabled_;

  tracing_enabled_ = tracing_possible_;
  tracing_ever_enabled_ = tracing_enabled_;

  if (old_tracing_enabled != tracing_enabled_) {
    tracing_enabled_changed_ = true;
  }
  return tracing_enabled_;
}

bool VerilatorSimCtrl::TraceOff() {
  if (tracing_enabled_) {
    tracing_enabled_changed_ = true;
  }
  tracing_enabled_ = false;
  return tracing_enabled_;
}

void VerilatorSimCtrl::PrintStatistics() const {
  double speed_hz = time_ / 2 / (GetExecutionTimeMs() / 1000.0);
  double speed_khz = speed_hz / 1000.0;

  std::cout << std::endl
            << "Simulation statistics" << std::endl
            << "=====================" << std::endl
            << "Executed cycles:  " << time_ / 2 << std::endl
            << "Wallclock time:   " << GetExecutionTimeMs() / 1000.0 << " s"
            << std::endl
            << "Simulation speed: " << speed_hz << " cycles/s "
            << "(" << speed_khz << " kHz)" << std::endl;

  int trace_size_byte;
  if (tracing_enabled_ && FileSize(GetTraceFileName(), trace_size_byte)) {
    std::cout << "Trace file size:  " << trace_size_byte << " B" << std::endl;
  }
}

const char *VerilatorSimCtrl::GetTraceFileName() const {
#ifdef VM_TRACE_FMT_FST
  return "sim.fst";
#else
  return "sim.vcd";
#endif
}

void VerilatorSimCtrl::Run() {
  assert(top_ && "Use SetTop() first.");

  // We always need to enable this as tracing can be enabled at runtime
  if (tracing_possible_) {
    Verilated::traceEverOn(true);
    top_->trace(tracer_, 99, 0);
  }

  // Evaluate all initial blocks, including the DPI setup routines
  top_->eval();

  std::cout << std::endl
            << "Simulation running, end by pressing CTRL-c." << std::endl;

  time_begin_ = std::chrono::steady_clock::now();
  UnsetReset();
  Trace();

  unsigned long start_reset_cycle_ = initial_reset_delay_cycles_;
  unsigned long end_reset_cycle_ = start_reset_cycle_ + reset_duration_cycles_;

  while (1) {
    unsigned long cycle_ = time_ / 2;

    if (cycle_ == start_reset_cycle_) {
      SetReset();
    } else if (cycle_ == end_reset_cycle_) {
      UnsetReset();
    }

    *sig_clk_ = !*sig_clk_;

    // Call all extension on-clock methods
    if (*sig_clk_) {
      for (auto it = extension_array_.begin(); it != extension_array_.end();
           ++it) {
        (*it)->OnClock(time_);
      }
    }

    top_->eval();
    time_++;

    Trace();

    if (request_stop_) {
      std::cout << "Received stop request, shutting down simulation."
                << std::endl;
      break;
    }
    if (Verilated::gotFinish()) {
      std::cout << "Received $finish() from Verilog, shutting down simulation."
                << std::endl;
      break;
    }
    if (term_after_cycles_ && (time_ / 2 >= term_after_cycles_)) {
      std::cout << "Simulation timeout of " << term_after_cycles_
                << " cycles reached, shutting down simulation." << std::endl;
      break;
    }
  }

  top_->final();
  time_end_ = std::chrono::steady_clock::now();

  if (TracingEverEnabled()) {
    tracer_.close();
  }
}

std::string VerilatorSimCtrl::GetName() const {
  if (top_) {
    return top_->name();
  }
  return "unknown";
}

unsigned int VerilatorSimCtrl::GetExecutionTimeMs() const {
  return std::chrono::duration_cast<std::chrono::milliseconds>(time_end_ -
                                                               time_begin_)
      .count();
}

void VerilatorSimCtrl::SetReset() {
  if (flags_ & ResetPolarityNegative) {
    *sig_rst_ = 0;
  } else {
    *sig_rst_ = 1;
  }
}

void VerilatorSimCtrl::UnsetReset() {
  if (flags_ & ResetPolarityNegative) {
    *sig_rst_ = 1;
  } else {
    *sig_rst_ = 0;
  }
}

bool VerilatorSimCtrl::FileSize(std::string filepath, int &size_byte) const {
  struct stat statbuf;
  if (stat(filepath.data(), &statbuf) != 0) {
    size_byte = 0;
    return false;
  }

  size_byte = statbuf.st_size;
  return true;
}

void VerilatorSimCtrl::Trace() {
  // We cannot output a message when calling TraceOn()/TraceOff() as these
  // functions can be called from a signal handler. Instead we print the message
  // here from the main loop.
  if (tracing_enabled_changed_) {
    if (TracingEnabled()) {
      std::cout << "Tracing enabled." << std::endl;
    } else {
      std::cout << "Tracing disabled." << std::endl;
    }
    tracing_enabled_changed_ = false;
  }

  if (!TracingEnabled()) {
    return;
  }

  if (!tracer_.isOpen()) {
    tracer_.open(GetTraceFileName());
    std::cout << "Writing simulation traces to " << GetTraceFileName()
              << std::endl;
  }

  tracer_.dump(GetTime());
}
