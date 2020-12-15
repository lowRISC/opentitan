// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <fstream>
#include <getopt.h>
#include <iomanip>
#include <iostream>
#include <memory>
#include <string>
#include <svdpi.h>

#include "log_trace_listener.h"
#include "otbn_memutil.h"
#include "otbn_trace_checker.h"
#include "otbn_trace_source.h"
#include "verilated_toplevel.h"
#include "verilator_memutil.h"
#include "verilator_sim_ctrl.h"

extern "C" {
extern unsigned int otbn_base_call_stack_get_size();
extern unsigned int otbn_base_call_stack_get_element(int index);
extern unsigned int otbn_base_reg_get(int index);
extern unsigned int otbn_bignum_reg_get(int index, int quarter);
}

/**
 * SimCtrlExtension that adds a '--otbn-trace-file' command line option. If set
 * it sets up a LogTraceListener that will dump out the trace to the given log
 * file
 */
class OtbnTraceUtil : public SimCtrlExtension {
 private:
  std::unique_ptr<LogTraceListener> log_trace_listener_;

  bool SetupTraceLog(const std::string &log_filename) {
    try {
      log_trace_listener_ = std::make_unique<LogTraceListener>(log_filename);
      OtbnTraceSource::get().AddListener(log_trace_listener_.get());
      return true;
    } catch (const std::runtime_error &err) {
      std::cerr << "ERROR: Failed to set up trace log: " << err.what()
                << std::endl;
      return false;
    }

    return false;
  }

  void PrintHelp() {
    std::cout << "Trace log utilities:\n\n"
                 "--otbn-trace-file=FILE\n"
                 "  Write OTBN trace log to FILE\n\n";
  }

 public:
  virtual bool ParseCLIArguments(int argc, char **argv, bool &exit_app) {
    const struct option long_options[] = {
        {"otbn-trace-file", required_argument, nullptr, 'l'},
        {"help", no_argument, nullptr, 'h'},
        {nullptr, no_argument, nullptr, 0}};

    // Reset the command parsing index in-case other utils have already parsed
    // some arguments
    optind = 1;
    while (1) {
      int c = getopt_long(argc, argv, "h", long_options, nullptr);
      if (c == -1) {
        break;
      }

      switch (c) {
        case 0:
          break;
        case 'l':
          return SetupTraceLog(optarg);
        case 'h':
          PrintHelp();
          break;
      }
    }

    return true;
  }

  ~OtbnTraceUtil() {
    if (log_trace_listener_)
      OtbnTraceSource::get().RemoveListener(log_trace_listener_.get());
  }
};

int main(int argc, char **argv) {
  otbn_top_sim top;

  VerilatorMemUtil memutil(new OtbnMemUtil("TOP.otbn_top_sim"));
  OtbnTraceUtil traceutil;

  VerilatorSimCtrl &simctrl = VerilatorSimCtrl::GetInstance();
  simctrl.SetTop(&top, &top.IO_CLK, &top.IO_RST_N,
                 VerilatorSimCtrlFlags::ResetPolarityNegative);
  simctrl.RegisterExtension(&memutil);
  simctrl.RegisterExtension(&traceutil);

  std::cout << "Simulation of OTBN" << std::endl
            << "==================" << std::endl
            << std::endl;

  auto pr = simctrl.Exec(argc, argv);
  int ret_code = pr.first;
  bool ran_simulation = pr.second;

  if (ret_code != 0 || !ran_simulation) {
    return ret_code;
  }

  svSetScope(svGetScopeFromName("TOP.otbn_top_sim"));

  svBit model_err = otbn_err_get();
  if (model_err) {
    return 1;
  }

  std::cout << "Call Stack:" << std::endl;
  std::cout << "-----------" << std::endl;
  for (int i = 0; i < otbn_base_call_stack_get_size(); ++i) {
    std::cout << std::setfill(' ') << "0x" << std::hex << std::setw(8)
              << std::setfill('0') << std::right
              << otbn_base_call_stack_get_element(i) << std::endl;
  }

  std::cout << std::endl;

  std::cout << "Final Base Register Values:" << std::endl;
  std::cout << "Reg | Value" << std::endl;
  std::cout << "----------------" << std::endl;
  for (int i = 2; i < 32; ++i) {
    std::cout << "x" << std::left << std::dec << std::setw(2)
              << std::setfill(' ') << i << " | 0x" << std::hex << std::setw(8)
              << std::setfill('0') << std::right << otbn_base_reg_get(i)
              << std::endl;
  }

  std::cout << std::endl;

  std::cout << "Final Bignum Register Values:" << std::endl;
  std::cout << "Reg | Value" << std::endl;
  std::cout << "---------------------------------------------------------------"
               "----------------"
            << std::endl;

  for (int i = 0; i < 32; ++i) {
    std::cout << "w" << std::left << std::dec << std::setw(2)
              << std::setfill(' ') << i << " | 0x" << std::hex;

    std::cout << std::setw(8) << std::setfill('0') << std::right
              << otbn_bignum_reg_get(i, 7) << "_";

    std::cout << std::setw(8) << std::setfill('0') << otbn_bignum_reg_get(i, 6)
              << "_";

    std::cout << std::setw(8) << std::setfill('0') << otbn_bignum_reg_get(i, 5)
              << "_";

    std::cout << std::setw(8) << std::setfill('0') << otbn_bignum_reg_get(i, 4)
              << "_";

    std::cout << std::setw(8) << std::setfill('0') << otbn_bignum_reg_get(i, 3)
              << "_";

    std::cout << std::setw(8) << std::setfill('0') << otbn_bignum_reg_get(i, 2)
              << "_";

    std::cout << std::setw(8) << std::setfill('0') << otbn_bignum_reg_get(i, 1)
              << "_";

    std::cout << std::setw(8) << std::setfill('0') << otbn_bignum_reg_get(i, 0)
              << std::endl;
  }

  return 0;
}
