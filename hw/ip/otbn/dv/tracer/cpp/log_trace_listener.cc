// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <cassert>
#include <iomanip>
#include <ios>
#include <sstream>
#include <stdexcept>
#include <string>

#include "log_trace_listener.h"

LogTraceListener::LogTraceListener(const std::string &log_filename)
    : trace_log(log_filename, std::fstream::out) {
  if (!trace_log.is_open()) {
    std::ostringstream oss;
    oss << "Could not open log file: " << log_filename;
    throw std::runtime_error(oss.str());
  }
}

void LogTraceListener::AcceptTraceString(const std::string &trace,
                                         unsigned int cycle_count) {
  assert(trace_log.is_open());

  // Split the trace up into a vector of strings, one per line
  auto trace_lines = SplitTraceLines(trace);

  // Write out the lines from the trace
  bool first_line = true;
  for (auto &line : trace_lines) {
    if (first_line) {
      if (line.size() > 1) {
        // It is expected the first line of any trace output is an 'E' or 'S'
        // line (instruction execute or instruction stall)
        bool is_e_or_s_line = line[0] == 'E' || line[0] == 'S';

        // Output the beginning of the first line adding a cycle count. A
        // special '!' line, only giving the cycle count, is output if the first
        // line isn't an 'E' or 'S' line.
        std::ios old_state(nullptr);
        old_state.copyfmt(trace_log);
        trace_log << (is_e_or_s_line ? line[0] : '!') << " " << std::setw(9)
                  << std::setfill('0') << cycle_count;
        trace_log.copyfmt(old_state);

        if (is_e_or_s_line) {
          // If this is an expected 'E' or 'S' line write the rest of it out
          trace_log << line.substr(1) << "\n";
        } else {
          // Otherwise leave the '!' line on it's own and dump this line out
          // indented.
          trace_log << "\n    " << line << "\n";
        }
      } else {
        trace_log << "ERR: Bad line at " << cycle_count
                  << " line should be more than 1 character: " << line << "\n";
      }

      first_line = false;
    } else {
      // All lines other than the first are indented.
      trace_log << "    " << line << "\n";
    }
  }
}
