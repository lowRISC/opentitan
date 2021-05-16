// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "otbn_trace_entry.h"

#include <algorithm>
#include <cassert>
#include <iostream>
#include <regex>
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

bool OtbnIssTraceEntry::from_iss_trace(const std::vector<std::string> &lines) {
  // Read FSM. state 0 = read header; state 1 = read mnemonic (for E
  // lines); state 2 = read writes
  int state = 0;

  std::regex re("# @0x([0-9a-f]{8}): (.*)");
  std::smatch match;

  for (const std::string &line : lines) {
    switch (state) {
      case 0:
        hdr_ = line;
        state = (!line.empty() && line[0] == 'E') ? 1 : 2;
        break;

      case 1:
        // This some "special" extra data from the ISS that we use for
        // functional coverage calculations. The line should be of the form
        //
        //  # @ADDR: MNEMONIC
        //
        // where ADDR is an 8-digit instruction address (in hex) and mnemonic
        // is the string mnemonic.
        if (!std::regex_match(line, match, re)) {
          std::cerr << "Bad 'special' line for ISS trace with header `" << hdr_
                    << "': `" << line << "'.\n";
          return false;
        }
        assert(match.size() == 3);
        data_.insn_addr =
            (uint32_t)strtoul(match[1].str().c_str(), nullptr, 16);
        data_.mnemonic = match[2].str();
        state = 2;
        break;

      default: {
        assert(state == 2);
        // Ignore '!' lines (which are used to tell the simulation about
        // external register changes, not tracked by the RTL core simulation)
        bool is_bang = (line.size() > 0 && line[0] == '!');
        if (!is_bang) {
          writes_.push_back(line);
        }
        break;
      }
    }
  }

  // We shouldn't be in state 1 here: that would mean an E line with no
  // follow-up '#' line.
  if (state == 1) {
    std::cerr << "No 'special' line for ISS trace with header `" << hdr_
              << "'.\n";
    return false;
  }

  std::sort(writes_.begin(), writes_.end());
  return true;
}
