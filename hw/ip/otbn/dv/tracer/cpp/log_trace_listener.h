// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_HW_IP_OTBN_DV_TRACER_CPP_LOG_TRACE_LISTENER_H_
#define OPENTITAN_HW_IP_OTBN_DV_TRACER_CPP_LOG_TRACE_LISTENER_H_

#include <fstream>
#include <string>

#include "otbn_trace_listener.h"

/**
 * An OtbnTraceListener that dumps the trace to a log file, with some minimal
 * pretty printing.
 *
 * It examines the first line of any trace output, expecting it to be an 'E' or
 * 'S' (execute or stall) line. If this is the case it adds a cycle count
 * following the 'E' or 'S' and then dumps the trace. Lines that follow in the
 * 'E' or 'S' line in the same clock cycle are indented by four spaces.
 *
 * If an 'E' or 'S' line isn't seen as the first line it prints a special '!'
 * line that gives the cycle count and dumps the rest of the trace indented by
 * four spaces.
 */
class LogTraceListener : public OtbnTraceListener {
 private:
  std::ofstream trace_log;

 public:
  /**
   * Constructor that takes a log filename to write trace output to. It throws
   * std::runtime_error if the file cannot be opened.
   */
  LogTraceListener(const std::string &log_filename);
  void AcceptTraceString(const std::string &trace,
                         unsigned int cycle_count) override;
};

#endif  // OPENTITAN_HW_IP_OTBN_DV_TRACER_CPP_LOG_TRACE_LISTENER_H_
