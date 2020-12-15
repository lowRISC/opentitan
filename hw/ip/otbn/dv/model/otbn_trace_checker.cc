// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "otbn_trace_checker.h"

#include <algorithm>
#include <cassert>
#include <iostream>
#include <memory>

#include "otbn_trace_source.h"

static std::unique_ptr<OtbnTraceChecker> trace_checker;

OtbnTraceChecker::OtbnTraceChecker()
    : rtl_pending_(false),
      rtl_stall_(false),
      iss_pending_(false),
      done_(true),
      seen_err_(false) {
  OtbnTraceSource::get().AddListener(this);
}

OtbnTraceChecker::~OtbnTraceChecker() {
  if (!done_) {
    std::cerr
        << ("WARNING: Destroying OtbnTraceChecker object with an "
            "unfinished operation.\n");
  }
}

OtbnTraceChecker &OtbnTraceChecker::get() {
  if (!trace_checker) {
    trace_checker.reset(new OtbnTraceChecker());
  }
  return *trace_checker;
}

void OtbnTraceChecker::AcceptTraceString(const std::string &trace,
                                         unsigned int cycle_count) {
  assert(!(rtl_pending_ && iss_pending_));

  if (seen_err_)
    return;

  done_ = false;
  TraceEntry trace_entry = TraceEntry::from_rtl_trace(trace);
  if (trace_entry.hdr_.empty()) {
    std::cerr << "ERROR: Invalid RTL trace entry with empty header:\n";
    trace_entry.print("  ", std::cerr);
    seen_err_ = true;
    return;
  }

  // Unless something has gone very wrong, trace_entry.hdr_ will start with 'S'
  // (stall) or 'E' (execute). We want to coalesce entries for an instruction
  // here to avoid the ISS needing to figure out what write happens when on a
  // multi-cycle instruction.
  //
  // We work on the basis that an instruction will appear as zero or more stall
  // entries followed by an execution entry. When we see a stall entry, we
  // merge it into rtl_stalled_entry_, setting rtl_stall_ to flag that it
  // contains some information.
  //
  // When an execution entry comes up, we check it matches the pending stall
  // entry and then merge all the fields together, finally setting
  // rtl_pending_.
  bool is_stall = trace_entry.hdr_[0] == 'S';
  if (is_stall) {
    if (rtl_stall_) {
      // We already have a stall line. Make sure the headers match.
      if (rtl_stalled_entry_.hdr_ != trace_entry.hdr_) {
        std::cerr
            << ("ERROR: Stall trace entry followed by "
                "mis-matching stall.\n"
                "  Existing stall entry was:\n");
        rtl_stalled_entry_.print("    ", std::cerr);
        std::cerr << "  New stall entry was:\n";
        trace_entry.print("    ", std::cerr);
        seen_err_ = true;
        return;
      }
      rtl_stalled_entry_.take_writes(trace_entry);
    } else {
      // This is the first stall. Set the rtl_stall_ flag and save trace_entry.
      rtl_stall_ = true;
      rtl_stalled_entry_ = trace_entry;
    }
    return;
  }

  // This wasn't a stall entry. Check it's an execution.
  if (trace_entry.hdr_[0] != 'E') {
    std::cerr << "ERROR: Invalid RTL trace entry (neither S nor E):\n";
    trace_entry.print("  ", std::cerr);
    seen_err_ = true;
    return;
  }

  // If had a stall before, merge in any writes from it, making sure the lines
  // match.
  if (rtl_stall_) {
    if (trace_entry.hdr_.compare(1, std::string::npos, rtl_stalled_entry_.hdr_,
                                 1, std::string::npos) != 0) {
      std::cerr
          << ("ERROR: Execution trace entry doesn't match stall:\n"
              "  Stall entry was:\n");
      rtl_stalled_entry_.print("    ", std::cerr);
      std::cerr << "  Execution entry was:\n";
      trace_entry.print("    ", std::cerr);
      seen_err_ = true;
      return;
    }

    trace_entry.take_writes(rtl_stalled_entry_);
  }

  // Check we don't already have a pending RTL execution entry
  if (rtl_pending_) {
    std::cerr
        << ("ERROR: Two back-to-back RTL "
            "trace entries with no ISS entry.\n"
            "  First RTL entry was:\n");
    rtl_entry_.print("    ", std::cerr);
    std::cerr << "  Second RTL entry was:\n";
    trace_entry.print("    ", std::cerr);
    seen_err_ = true;
    return;
  }

  rtl_pending_ = true;
  rtl_stall_ = false;
  rtl_entry_ = trace_entry;

  if (!MatchPair()) {
    seen_err_ = true;
  }
}

bool OtbnTraceChecker::OnIssTrace(const std::vector<std::string> &lines) {
  assert(!(rtl_pending_ && iss_pending_));

  if (seen_err_) {
    return false;
  }

  // Ignore STALL entries
  if (lines.size() == 1 && lines[0] == "STALL") {
    return true;
  }

  TraceEntry trace_entry = TraceEntry::from_iss_trace(lines);

  done_ = false;
  if (iss_pending_) {
    std::cerr
        << ("ERROR: Two back-to-back ISS "
            "trace entries with no RTL entry.\n"
            "  First ISS entry was:\n");
    iss_entry_.print("    ", std::cerr);
    std::cerr << "  Second ISS entry was:\n";
    trace_entry.print("    ", std::cerr);
    seen_err_ = true;
    return false;
  }
  iss_pending_ = true;
  iss_entry_ = trace_entry;

  return MatchPair();
}

bool OtbnTraceChecker::Finish() {
  assert(!(rtl_pending_ && iss_pending_));
  done_ = true;
  if (seen_err_) {
    return false;
  }
  if (iss_pending_) {
    std::cerr
        << ("ERROR: Got to end of RTL operation, but there is no RTL "
            "trace entry to match the pending ISS one:\n");
    iss_entry_.print("    ", std::cerr);
    seen_err_ = true;
    return false;
  }
  if (rtl_pending_) {
    std::cerr
        << ("ERROR: Got to end of ISS operation, but there is no ISS "
            "trace entry to match the pending RTL one:\n");
    rtl_entry_.print("    ", std::cerr);
    seen_err_ = true;
    return false;
  }
  return true;
}

bool OtbnTraceChecker::MatchPair() {
  if (!(rtl_pending_ && iss_pending_)) {
    return true;
  }
  rtl_pending_ = false;
  iss_pending_ = false;
  if (!(rtl_entry_ == iss_entry_)) {
    std::cerr
        << ("ERROR: Mismatch between RTL and ISS trace entries.\n"
            "  RTL entry is:\n");
    rtl_entry_.print("    ", std::cerr);
    std::cerr << "  ISS entry is:\n";
    iss_entry_.print("    ", std::cerr);
    seen_err_ = true;
    return false;
  }
  return true;
}

OtbnTraceChecker::TraceEntry OtbnTraceChecker::TraceEntry::from_rtl_trace(
    const std::string &trace) {
  TraceEntry entry;

  size_t eol = trace.find('\n');
  entry.hdr_ = trace.substr(0, eol);

  while (eol != std::string::npos) {
    size_t bol = eol + 1;
    eol = trace.find('\n', bol);
    size_t line_len =
        (eol == std::string::npos) ? std::string::npos : eol - bol;
    std::string line = trace.substr(bol, line_len);
    if (line.size() > 0 && line[0] == '>')
      entry.writes_.push_back(line);
  }
  std::sort(entry.writes_.begin(), entry.writes_.end());

  return entry;
}

OtbnTraceChecker::TraceEntry OtbnTraceChecker::TraceEntry::from_iss_trace(
    const std::vector<std::string> &lines) {
  TraceEntry entry;
  if (!lines.empty()) {
    entry.hdr_ = lines[0];
  }
  bool first = true;
  for (const std::string &line : lines) {
    if (first) {
      entry.hdr_ = line;
    } else {
      // Ignore '!' lines (which are used to tell the simulation about external
      // register changes, not tracked by the RTL core simulation)
      bool is_bang = (line.size() > 0 && line[0] == '!');
      if (!is_bang) {
        entry.writes_.push_back(line);
      }
    }
    first = false;
  }
  std::sort(entry.writes_.begin(), entry.writes_.end());
  return entry;
}

bool OtbnTraceChecker::TraceEntry::operator==(const TraceEntry &other) const {
  return hdr_ == other.hdr_ && writes_ == other.writes_;
}

void OtbnTraceChecker::TraceEntry::print(const std::string &indent,
                                         std::ostream &os) const {
  os << indent << hdr_ << "\n";
  for (const std::string &write : writes_) {
    os << indent << write << "\n";
  }
}

void OtbnTraceChecker::TraceEntry::take_writes(const TraceEntry &other) {
  if (!other.writes_.empty()) {
    for (const std::string &write : other.writes_) {
      writes_.push_back(write);
    }
    std::sort(writes_.begin(), writes_.end());
  }
}
