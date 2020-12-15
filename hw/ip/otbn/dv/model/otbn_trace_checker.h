// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#pragma once

// A singleton class that listens to trace entries from the simulated core (as
// an OtbnTraceListener) and compares them with the trace coming out of the
// stepped ISS process.
//
// Trace entries from the simulated core appear as a result of DPI callbacks,
// so there's no way to propagate errors when they appear. ISS trace entries
// arrive through a synchronous interface, so the checker reports any mismatch
// at that point.
//
// For example, if "RTL A" means "trace event A from RTL" and "ISS B" means
// "trace event B from ISS" then the following is a correct series of trace
// events:
//
//     RTL A; ISS A; ISS B; RTL B ...
//
// None of these are valid:
//
//     RTL A; RTL B; ...  (*)
//     ISS A; ISS B; ...
//     RTL A; ISS B; ...
//
// The only way that an invalid trace is not reported is if no ISS trace events
// appear after the error. Trace (*), above, is an example of this. Another
// example would be if the last trace events were one of:
//
//     ...; ISS A; RTL B
//     ...; ISS A           (and nothing else)
//
// To catch these cases, the ISS simulation must call the Finish() method when
// it is done (which checks there are no outstanding events missing).

#include <iosfwd>
#include <string>
#include <vector>

#include "otbn_trace_listener.h"

class OtbnTraceChecker : public OtbnTraceListener {
 public:
  OtbnTraceChecker();
  ~OtbnTraceChecker();

  // Get the singleton object
  static OtbnTraceChecker &get();

  // Take a trace entry from the wrapped RTL. Any mismatch error is stored
  // until the next call to an API function that can respond with the error.
  void AcceptTraceString(const std::string &trace,
                         unsigned int cycle_count) override;

  // Take a trace entry from the wrapped ISS.
  //
  // Prints an error message to stderr and returns false on mismatch.
  bool OnIssTrace(const std::vector<std::string> &lines);

  // Call this when the ISS simulation completes an operation (on ECALL or
  // error).
  //
  // Prints an error message to stderr and returns false if it detects a
  // mismatch.
  bool Finish();

 private:
  // If rtl_pending_ and iss_pending_ are not both true, return true
  // immediately with no other change. Otherwise, compare the two pending trace
  // entries. If they match, clear them both and return true. If not, print a
  // message to stderr and return false.
  bool MatchPair();

  class TraceEntry {
   public:
    static TraceEntry from_rtl_trace(const std::string &trace);
    static TraceEntry from_iss_trace(const std::vector<std::string> &lines);

    bool operator==(const TraceEntry &other) const;
    void print(const std::string &indent, std::ostream &os) const;

    void take_writes(const TraceEntry &other);

    std::string hdr_;
    std::vector<std::string> writes_;
  };

  bool rtl_pending_;
  bool rtl_stall_;
  TraceEntry rtl_entry_;
  TraceEntry rtl_stalled_entry_;

  bool iss_pending_;
  TraceEntry iss_entry_;

  bool done_;
  bool seen_err_;
};
