// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#pragma once

#include <cstdint>
#include <cstdio>
#include <string>
#include <unistd.h>
#include <vector>

// An object wrapping the ISS subprocess.
struct ISSWrapper {
  ISSWrapper();
  ~ISSWrapper();

  // No copy constructor or assignments: we're wrapping a child process.
  ISSWrapper(const ISSWrapper &) = delete;
  ISSWrapper &operator=(const ISSWrapper &) = delete;

  // Load new contents of DMEM / IMEM
  void load_d(const char *path);
  void load_i(const char *path);

  // Dump the contents of DMEM to a file
  void dump_d(const char *path) const;

  // Jump to a new address and start running
  void start(uint32_t addr);

  // Run simulation until ECALL or error. Return the number of cycles
  // until that happened.
  size_t run();

 private:
  // Read line by line from the child process until we get ".\n".
  // Return true if we got the ".\n" terminator, false if EOF. If dst
  // is not null, append to it each line that was read.
  bool read_child_response(std::vector<std::string> *dst) const;

  // Send a command to the child and wait for its response. Return
  // value and dst argument behave as for read_child_response.
  bool run_command(const std::string &cmd, std::vector<std::string> *dst) const;

  // Return true if lines contain a line that shows otbn.STATUS having
  // its busy flag cleared.
  bool saw_busy_cleared(std::vector<std::string> &lines) const;

  pid_t child_pid;
  FILE *child_write_file;
  FILE *child_read_file;
};
