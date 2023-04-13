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

#include "Votbn_top_sim__Syms.h"
#include "log_trace_listener.h"
#include "otbn_memutil.h"
#include "otbn_model.h"
#include "otbn_trace_checker.h"
#include "otbn_trace_source.h"
#include "sv_scoped.h"
#include "verilated_toplevel.h"
#include "verilator_memutil.h"
#include "verilator_sim_ctrl.h"

extern "C" {
extern unsigned int otbn_base_call_stack_get_size();
extern unsigned int otbn_base_call_stack_get_element(int index);
extern unsigned int otbn_base_reg_get(int index);
extern unsigned int otbn_bignum_reg_get(int index, int quarter);
extern svBit otbn_err_get();
extern int otbn_core_get_stop_pc();
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
      log_trace_listener_.reset(new LogTraceListener(log_filename));
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
      int c = getopt_long(argc, argv, "-h", long_options, nullptr);
      if (c == -1) {
        break;
      }

      switch (c) {
        case 0:
        case 1:
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

static otbn_top_sim *verilator_top;
static OtbnMemUtil otbn_memutil("TOP.otbn_top_sim");

int main(int argc, char **argv) {
  VerilatorMemUtil memutil(&otbn_memutil);
  OtbnTraceUtil traceutil;

  otbn_top_sim top;
  // Make the otbn_top_sim object visible to OtbnTopApplyLoopWarp.
  // This will leave a dangling pointer when we exit main, but that
  // doesn't really matter because we don't have anything that uses it
  // running in atexit hooks.
  verilator_top = &top;

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

  int exp_stop_pc = otbn_memutil.GetExpEndAddr();
  if (exp_stop_pc >= 0) {
    SVScoped core_scope("TOP.otbn_top_sim.u_otbn_core_model");
    int act_stop_pc = otbn_core_get_stop_pc();
    if (exp_stop_pc != act_stop_pc) {
      std::cerr << "ERROR: Expected stop PC from ELF file was 0x" << std::hex
                << exp_stop_pc << ", but simulation actually stopped at 0x"
                << act_stop_pc << ".\n";
      return 1;
    }
  }

  return 0;
}

// This is executed over DPI on the first posedge of the clock after each
// reset. It's in charge of telling the model about any loop warp symbols in
// the ELF file.
extern "C" int OtbnTopInstallLoopWarps() {
  // Cast to the right base class of otbn_top_sim. Otherwise, you can't access
  // the "otbn_top_sim" member because you get the derived class's constructor
  // by accident.
  Votbn_top_sim &top = *verilator_top;

  // Grab the model handle from the otbn_core_model module. This should have
  // been initialised by now because it gets set up in an initial block and
  // this code doesn't run until the first clock edge.
  auto sv_model_handle = top.otbn_top_sim->u_otbn_core_model->model_handle;

  // sv_model_handle will be some integer type. Check it's nonzero and, if so,
  // convert it to an OtbnModel*.
  assert(sv_model_handle != 0);

  OtbnModel *model_handle = (OtbnModel *)sv_model_handle;

  if (model_handle->take_loop_warps(otbn_memutil) != 0) {
    // Something went wrong when trying to update the model. We've already
    // written to something to stderr, so should just pass the non-zero return
    // value up the stack.
    return -1;
  }

  return 0;
}

template <typename PrimCountT>
void set_up_down_prim_count(PrimCountT *prim_count, uint32_t new_cnt) {
  // There are two counters within this primitive: The primary counter gives
  // the remaining iterations and the secondary counter counts in reverse
  // direction. They must always sum to the constant value 2**Width-1, which is
  // 2**32-1 = 0xFFFFFFFF in this case.

  // Loop warping occurs on the negative clock edge. When writing signal values
  // here that won't trigger any processes within the verilator simulation. At
  // the next positive clock edge @(posedge clk) processes will run before any
  // _d update processes so write the relevant _d values here.

  auto up_cnt_flop = prim_count->gen_cnts__BRA__0__KET____DOT__u_cnt_flop;
  auto down_cnt_flop = prim_count->gen_cnts__BRA__1__KET____DOT__u_cnt_flop;

  up_cnt_flop->gen_generic__DOT__u_impl_generic->d_i = new_cnt;
  down_cnt_flop->gen_generic__DOT__u_impl_generic->d_i = 0xFFFFFFFF - new_cnt;
}

template <typename LoopControllerT>
auto get_loop_counter(LoopControllerT *loop_controller, uint32_t counter_idx)
    -> decltype(loop_controller
                    ->g_loop_counters__BRA__0__KET____DOT__u_loop_count) {
  assert(counter_idx < 8);

  switch (counter_idx) {
    case 0:
      return loop_controller->g_loop_counters__BRA__0__KET____DOT__u_loop_count;
    case 1:
      return loop_controller->g_loop_counters__BRA__1__KET____DOT__u_loop_count;
    case 2:
      return loop_controller->g_loop_counters__BRA__2__KET____DOT__u_loop_count;
    case 3:
      return loop_controller->g_loop_counters__BRA__3__KET____DOT__u_loop_count;
    case 4:
      return loop_controller->g_loop_counters__BRA__4__KET____DOT__u_loop_count;
    case 5:
      return loop_controller->g_loop_counters__BRA__5__KET____DOT__u_loop_count;
    case 6:
      return loop_controller->g_loop_counters__BRA__6__KET____DOT__u_loop_count;
    case 7:
      return loop_controller->g_loop_counters__BRA__7__KET____DOT__u_loop_count;
    default:
      return nullptr;
  }
}

// This is executed over DPI on every negedge of the clock and is in charge of
// updating the top of the loop stack if necessary to match loop warp symbols
// in the ELF file.
extern "C" void OtbnTopApplyLoopWarp() {
  static std::vector<uint32_t> loop_count_stack;

  // See not in OtbnTopInstallLoopWarps for why this upcast is needed.
  Votbn_top_sim &top = *verilator_top;

  auto loop_controller =
      top.otbn_top_sim->u_otbn_core->u_otbn_controller->u_otbn_loop_controller;

  // Track loop stack state.
  if (loop_controller->current_loop_finish) {
    assert(!loop_count_stack.empty());
    loop_count_stack.pop_back();
  }
  if (loop_controller->loop_start_req_i &&
      loop_controller->loop_start_commit_i) {
    loop_count_stack.push_back(loop_controller->loop_iterations_i);
  }

  if (!loop_count_stack.empty()) {
    // There is a loop that's currently active. Its iteration count for the
    // next cycle is provided to the prefetcher via `prefetch_loop_iterations_o`
    // which we capture here.
    uint32_t total = loop_count_stack.back();
    uint32_t old_iters = loop_controller->prefetch_loop_iterations_o;

    // The RTL's view of "iterations remaining" counts down rather than up and
    // for the final iteration the count will be 1 (not zero). Convert to the
    // indexing we use in loop warp symbols (counting up, starting at zero) by
    // subtracting old_iters_d from total. The result should never be negative
    // (unless we messed up something somewhere).
    assert(old_iters <= total);

    uint32_t old_cnt = total - old_iters;
    uint32_t insn_addr = loop_controller->insn_addr_i;

    uint32_t new_cnt = otbn_memutil.GetLoopWarp(insn_addr, old_cnt);
    if (old_cnt != new_cnt) {
      // Convert from new_cnt back to the "iters" format by subtracting from
      // the total, but bottom out at 1 (the last iteration).
      uint32_t new_iters = (new_cnt < total) ? (total - new_cnt) : 1;

      set_up_down_prim_count(
          get_loop_counter(loop_controller,
                           (uint32_t)loop_controller->loop_stack_rd_idx),
          new_iters);
    }
  }
}

// This is executed over DPI when the model says that execution has just
// finished. We use it to dump out the current RTL state before secure wipe
// zeroes everything out.
extern "C" void OtbnTopDumpState() {
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
}
