// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#pragma once

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

  // Dump the contents of DMEM to a file
  void dump_d(const std::string &path) const;

  // Jump to a new address and start running
  void start(uint32_t addr);

  // Run simulation for a single cycle. Return true if it is now
  // finished (ECALL or error).
  //
  // If gen_trace is true, pass trace data to the (singleton)
  // OtbnTraceChecker object.
  std::pair<bool, uint32_t> step(bool gen_trace);

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

  // Send a command to the child and wait for its response. Return
  // value and dst argument behave as for read_child_response.
  bool run_command(const std::string &cmd, std::vector<std::string> *dst) const;

  pid_t child_pid;
  FILE *child_write_file;
  FILE *child_read_file;

  // A temporary directory for communicating with the child process
  std::unique_ptr<TmpDir> tmpdir;
};
