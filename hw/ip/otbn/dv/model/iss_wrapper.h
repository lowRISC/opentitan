// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#ifndef OPENTITAN_HW_IP_OTBN_DV_MODEL_ISS_WRAPPER_H_
#define OPENTITAN_HW_IP_OTBN_DV_MODEL_ISS_WRAPPER_H_

#include <array>
#include <cstdint>
#include <cstdio>
#include <memory>
#include <string>
#include <unistd.h>
#include <vector>

// Forward declaration (the implementation is private in iss_wrapper.cc)
struct TmpDir;

// An object wrapping the ISS subprocess.
struct ISSWrapper {
  // A 256-bit unsigned integer value, stored in "LSB order". Thus, words[0]
  // contains the LSB and words[7] contains the MSB.
  struct u256_t {
    uint32_t words[256 / 32];
  };

  ISSWrapper();
  ~ISSWrapper();

  // Load new contents of DMEM / IMEM
  void load_d(const std::string &path);
  void load_i(const std::string &path);

  // Add a loop warp instruction to the simulation
  void add_loop_warp(uint32_t addr, uint32_t from_cnt, uint32_t to_cnt);

  // Clear any loop warp instructions from the simulation
  void clear_loop_warps();

  // Dump the contents of DMEM to a file
  void dump_d(const std::string &path) const;

  // Jump to a new address and start running
  void start(uint32_t addr);

  // Provide data for RND. ISS will stall when RND is read and RND data isn't
  // available
  void edn_rnd_data(uint32_t edn_rnd_data[8]);

  // Signal URND reseed at beginning of execution is complete
  void edn_urnd_reseed_complete();

  // Run simulation for a single cycle. Returns a pair (ret_code, err_bits).
  //
  // If gen_trace is true, pass trace data to the (singleton)
  // OtbnTraceChecker object.
  //
  // ret_code describes the state of the simulation. It is 1 if the simulation
  // just stopped (on ECALL or an architectural error); it is 0 if the
  // simulation is still running. It is -1 if something went wrong (such as a
  // trace mismatch).
  //
  // err_bits is zero unless the simulation just came to a halt, in which case
  // it's the value of the ERR_BITS register.
  int step(bool gen_trace);

  // Reset simulation
  //
  // This doesn't actually send anything to the ISS, but instead tells
  // the OtbnTraceChecker to clear out any partial instructions
  void reset(bool gen_trace);

  // Get the current value of otbn.INSN_CNT. This should be called just after
  // step (but doesn't necessarily need to wait until the run has finished).
  uint32_t get_insn_cnt() const { return insn_cnt_; }

  // Get the err_bits from a run that's just finished. This should be
  // called just after step() returns 1.
  uint32_t get_err_bits() const { return err_bits_; }

  // Get the final PC from a run that's just finished. This should be
  // called just after step() returns 1.
  uint32_t get_stop_pc() const { return stop_pc_; }

  // Read contents of the register file
  void get_regs(std::array<uint32_t, 32> *gprs, std::array<u256_t, 32> *wdrs);

  // Read the contents of the call stack
  std::vector<uint32_t> get_call_stack();

  // Resolve a path relative to the convenience temporary directory.
  // relative should be a relative path (it is just appended to the
  // path of the temporary directory).
  std::string make_tmp_path(const std::string &relative) const;

 private:
  // Read line by line from the child process until we get ".\n".
  // Return true if we got the ".\n" terminator, false if EOF. If dst
  // is not null, append to it each line that was read.
  bool read_child_response(std::vector<std::string> *dst) const;

  // Send a command to the child and wait for its response. If no
  // response, raise a runtime_error.
  void run_command(const std::string &cmd, std::vector<std::string> *dst) const;

  pid_t child_pid;
  FILE *child_write_file;
  FILE *child_read_file;

  // A temporary directory for communicating with the child process
  std::unique_ptr<TmpDir> tmpdir;

  // INSN_CNT for the current run if there is one, or the previous run if
  // there's no current one.
  uint32_t insn_cnt_;

  // ERR_BITS and STOP_PC values from a run that's just finished.
  uint32_t err_bits_;
  uint32_t stop_pc_;
};

#endif  // OPENTITAN_HW_IP_OTBN_DV_MODEL_ISS_WRAPPER_H_
