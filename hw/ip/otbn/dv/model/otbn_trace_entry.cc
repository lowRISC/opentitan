// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "otbn_trace_entry.h"

#include <algorithm>
#include <sstream>

void OtbnTraceEntry::from_rtl_trace(const std::string &trace) {
  size_t eol = trace.find('\n');
  hdr_ = trace.substr(0, eol);

  while (eol != std::string::npos) {
    size_t bol = eol + 1;
    eol = trace.find('\n', bol);
    size_t line_len =
        (eol == std::string::npos) ? std::string::npos : eol - bol;
    std::string line = trace.substr(bol, line_len);
    if (line.size() > 0 && line[0] == '>')
      writes_.push_back(line);
  }
  std::sort(writes_.begin(), writes_.end());
}

void OtbnTraceEntry::from_iss_trace(const std::vector<std::string> &lines) {
  bool first = true;
  for (const std::string &line : lines) {
    if (first) {
      hdr_ = line;
    } else {
      // Ignore '!' lines (which are used to tell the simulation about external
      // register changes, not tracked by the RTL core simulation)
      bool is_bang = (line.size() > 0 && line[0] == '!');
      if (!is_bang) {
        writes_.push_back(line);
      }
    }
    first = false;
  }
  std::sort(writes_.begin(), writes_.end());
}

bool OtbnTraceEntry::operator==(const OtbnTraceEntry &other) const {
  return hdr_ == other.hdr_ && writes_ == other.writes_;
}

void OtbnTraceEntry::print(const std::string &indent, std::ostream &os) const {
  os << indent << hdr_ << "\n";
  for (const std::string &write : writes_) {
    os << indent << write << "\n";
  }
}

void OtbnTraceEntry::take_writes(const OtbnTraceEntry &other) {
  if (!other.writes_.empty()) {
    for (const std::string &write : other.writes_) {
      writes_.push_back(write);
    }
    std::sort(writes_.begin(), writes_.end());
  }
}

bool OtbnTraceEntry::empty() const { return hdr_.empty(); }

bool OtbnTraceEntry::is_stall() const { return !empty() && hdr_[0] == 'S'; }

bool OtbnTraceEntry::is_exec() const { return !empty() && hdr_[0] == 'E'; }

bool OtbnTraceEntry::is_compatible(const OtbnTraceEntry &prev) const {
  return 0 ==
         hdr_.compare(1, std::string::npos, prev.hdr_, 1, std::string::npos);
}
