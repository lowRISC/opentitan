// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "verilator_sim_ctrl.h"

#include <getopt.h>
#include <sys/stat.h>
#include <unistd.h>
#include <vltstd/svdpi.h>

#include <iostream>

// This is defined by Verilator and passed through the command line
#ifndef VM_TRACE
#define VM_TRACE 0
#endif

// DPI Exports
extern "C" {
extern void simutil_verilator_memload(const char* file);
}

VerilatorSimCtrl::VerilatorSimCtrl(VerilatedToplevel* top, CData& sig_clk,
                                   CData& sig_rst, VerilatorSimCtrlFlags flags)
    : top_(top),
      sig_clk_(sig_clk),
      sig_rst_(sig_rst),
      flags_(flags),
      time_(0),
      init_rom_(false),
      init_ram_(false),
      init_flash_(false),
      tracing_enabled_(false),
      tracing_enabled_changed_(false),
      tracing_ever_enabled_(false),
      tracing_possible_(VM_TRACE),
      initial_reset_delay_cycles_(2),
      reset_duration_cycles_(2),
      request_stop_(false),
      tracer_(VerilatedTracer()),
      term_after_cycles_(0) {}

void VerilatorSimCtrl::RequestStop() { request_stop_ = true; }

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

void VerilatorSimCtrl::PrintHelp() const {
  std::cout << "Execute a simulation model for " << top_->name()
            << "\n"
               "\n";
  if (tracing_possible_) {
    std::cout << "-t|--trace             Write a trace file from the start\n";
  }
  std::cout << "-r|--rominit=VMEMFILE  Initialize the ROM with VMEMFILE\n"
               "-m|--raminit=VMEMFILE  Initialize the RAM with VMEMFILE\n"
               "-f|--flashinit=VMEMFILE  Initialize the FLASH with VMEMFILE\n"
               "-h|--help              Show help\n"
               "\n"
               "All further arguments are passed to the design and can be used "
               "in the \n"
               "design, e.g. by DPI modules.\n";
}

void VerilatorSimCtrl::InitRom(std::string rom) {
  if (!init_rom_) {
    return;
  }

  svScope scope;

  scope = svGetScopeFromName(rom.data());
  if (!scope) {
    std::cerr << "ERROR: No ROM found at " << rom << std::endl;
    exit(1);
  }
  svSetScope(scope);

  simutil_verilator_memload(rom_init_file_.data());

  std::cout << std::endl
            << "Rom initialized with program at " << rom_init_file_
            << std::endl;
}

void VerilatorSimCtrl::InitRam(std::string ram) {
  if (!init_ram_) {
    return;
  }

  svScope scope;

  scope = svGetScopeFromName(ram.data());
  if (!scope) {
    std::cerr << "ERROR: No RAM found at " << ram << std::endl;
    exit(1);
  }
  svSetScope(scope);

  simutil_verilator_memload(ram_init_file_.data());

  std::cout << std::endl
            << "Ram initialized with program at " << ram_init_file_
            << std::endl;
}

void VerilatorSimCtrl::InitFlash(std::string flash) {
  if (!init_flash_) {
    return;
  }

  svScope scope;

  scope = svGetScopeFromName(flash.data());
  if (!scope) {
    std::cerr << "ERROR: No FLASH found at " << flash << std::endl;
    exit(1);
  }
  svSetScope(scope);

  simutil_verilator_memload(flash_init_file_.data());

  std::cout << std::endl
            << "Flash initialized with program at " << flash_init_file_
            << std::endl;
}

bool VerilatorSimCtrl::ParseCommandArgs(int argc, char** argv, int& retcode) {
  const struct option long_options[] = {
      {"rominit",   required_argument, nullptr, 'r'},
      {"raminit",   required_argument, nullptr, 'm'},
      {"flashinit", required_argument, nullptr, 'f'},
      {"term-after-cycles", required_argument, nullptr, 'c'},
      {"trace",     no_argument,       nullptr, 't'},
      {"help",      no_argument,       nullptr, 'h'},
      {nullptr,     no_argument,       nullptr, 0}};

  while (1) {
    int c = getopt_long(argc, argv, ":r:m:f:th", long_options, nullptr);
    if (c == -1) {
      break;
    }

    // Disable error reporting by getopt
    opterr = 0;

    switch (c) {
      case 0:
        break;
      case 'r':
        rom_init_file_ = optarg;
        init_rom_ = true;
        if (!IsFileReadable(rom_init_file_)) {
          std::cerr << "ERROR: ROM initialization file "
                    << "'" << rom_init_file_ << "'"
                    << " is not readable." << std::endl;
          return false;
        }
        break;
      case 'm':
        ram_init_file_ = optarg;
        init_ram_ = true;
        if (!IsFileReadable(ram_init_file_)) {
          std::cerr << "ERROR: Memory initialization file "
                    << "'" << ram_init_file_ << "'"
                    << " is not readable." << std::endl;
          return false;
        }
        break;
      case 'f':
        flash_init_file_ = optarg;
        init_flash_ = true;
        if (!IsFileReadable(flash_init_file_)) {
          std::cerr << "ERROR: FLASH initialization file "
                    << "'" << flash_init_file_ << "'"
                    << " is not readable." << std::endl;
          return false;
        }
        break;
      case 't':
        if (!tracing_possible_) {
          std::cerr << "ERROR: Tracing has not been enabled at compile time."
                    << std::endl;
          return false;
        }
        TraceOn();
        break;
      case 'c':
        term_after_cycles_ = atoi(optarg);
        break;
      case 'h':
        PrintHelp();
        return false;
      case ':':  // missing argument
        std::cerr << "ERROR: Missing argument." << std::endl;
        PrintHelp();
        return false;
      case '?':
      default:;
        // Ignore unrecognized options since they might be consumed by
        // Verilator's built-in parsing below.
    }
  }

  Verilated::commandArgs(argc, argv);
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
    tracer_.open(GetSimulationFileName());
    std::cout << "Writing simulation traces to " << GetSimulationFileName()
              << std::endl;
  }

  tracer_.dump(GetTime());
}

const char* VerilatorSimCtrl::GetSimulationFileName() const {
#ifdef VM_TRACE_FMT_FST
  return "sim.fst";
#else
  return "sim.vcd";
#endif
}

void VerilatorSimCtrl::Run() {
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
  while (1) {
    if (time_ >= initial_reset_delay_cycles_ * 2) {
      SetReset();
    }
    if (time_ >= reset_duration_cycles_ * 2 + initial_reset_delay_cycles_ * 2) {
      UnsetReset();
    }

    sig_clk_ = !sig_clk_;

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
    if (term_after_cycles_ && time_ > term_after_cycles_) {
      std::cout << "Simulation timeout of " << term_after_cycles_
                << " cycles reached, shutting down simulation."
                << std::endl;
      break;
    }
  }

  top_->final();
  time_end_ = std::chrono::steady_clock::now();

  if (TracingEverEnabled()) {
    tracer_.close();
  }
}

void VerilatorSimCtrl::SetReset() {
  if (flags_ & ResetPolarityNegative) {
    sig_rst_ = 0;
  } else {
    sig_rst_ = 1;
  }
}

void VerilatorSimCtrl::UnsetReset() {
  if (flags_ & ResetPolarityNegative) {
    sig_rst_ = 1;
  } else {
    sig_rst_ = 0;
  }
}

void VerilatorSimCtrl::SetInitialResetDelay(unsigned int cycles) {
  initial_reset_delay_cycles_ = cycles;
}

void VerilatorSimCtrl::SetResetDuration(unsigned int cycles) {
  reset_duration_cycles_ = cycles;
}

bool VerilatorSimCtrl::IsFileReadable(std::string filepath) {
  struct stat statbuf;
  return stat(filepath.data(), &statbuf) == 0;
}

bool VerilatorSimCtrl::FileSize(std::string filepath, int& size_byte) {
  struct stat statbuf;
  if (stat(filepath.data(), &statbuf) != 0) {
    size_byte = 0;
    return false;
  }

  size_byte = statbuf.st_size;
  return true;
}

unsigned int VerilatorSimCtrl::GetExecutionTimeMs() {
  return std::chrono::duration_cast<std::chrono::milliseconds>(time_end_ -
                                                               time_begin_)
      .count();
}

void VerilatorSimCtrl::PrintStatistics() {
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
  if (tracing_enabled_ && FileSize(GetSimulationFileName(), trace_size_byte)) {
    std::cout << "Trace file size:  " << trace_size_byte << " B" << std::endl;
  }
}
