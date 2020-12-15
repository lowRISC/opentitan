// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_HW_IP_OTBN_DV_TRACER_CPP_OTBN_TRACE_LISTENER_H_
#define OPENTITAN_HW_IP_OTBN_DV_TRACER_CPP_OTBN_TRACE_LISTENER_H_

#include <sstream>
#include <string>
#include <vector>

/**
 * Base class for anything that wants to examine trace output from OTBN. The
 * simulation that hosts the tracer is responsible for setting up listeners and
 * routing the DPI `accept_otbn_trace_string` calls to them.
 */
class OtbnTraceListener {
 public:
  /**
   * Helper function to split an OTBN trace output up into individual lines.
   *
   * @param trace Trace output from OTBN
   * @return A vector of lines from the trace
   */
  static std::vector<std::string> SplitTraceLines(const std::string &trace) {
    std::stringstream trace_ss(trace);
    std::string trace_line;

    std::vector<std::string> trace_lines;

    while (std::getline(trace_ss, trace_line, '\n')) {
      trace_lines.push_back(trace_line);
    }

    return trace_lines;
  }

  /**
   * Called to process an OTBN trace output, called a maximum of once per cycle
   *
   * @param trace Trace output from OTBN
   * @param cycle_count The cycle count associated with the trace output
   */
  virtual void AcceptTraceString(const std::string &trace,
                                 unsigned int cycle_count) = 0;
  virtual ~OtbnTraceListener() {}
};

#endif  // OPENTITAN_HW_IP_OTBN_DV_TRACER_CPP_OTBN_TRACE_LISTENER_H_
