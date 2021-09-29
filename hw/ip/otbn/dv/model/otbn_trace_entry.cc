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

bool OtbnIssTraceEntry::is_model_of(const OtbnTraceEntry &other) const {
  if (writes_ != other.get_writes())
    return false;

  // The writes match. How about the header line? If the two strings are
  // exactly equal, we're good.
  if (hdr_ == other.get_header())
    return true;

  // Otherwise, we might still be ok if our header is of the form 'FOO ???' and
  // the other header is of the form 'FOO BAR'. We don't support anything
  // particularly clever here: our header must end in one or more '?' signs
  // and, if so, we require the other header to start match that prefix.
  //
  // Firstly, is there a question mark at all?
  size_t last_question = hdr_.find_last_of('?');
  if (last_question == std::string::npos) {
    // Our line doesn't have a '?'. Give up.
    return false;
  }
  // Now, is that really at the end of the string? (That is, we want to allow
  // 'FOO???', but not 'FOO??BAR')
  size_t post_question = hdr_.find_first_not_of('?', last_question + 1);
  if (post_question != std::string::npos) {
    // There was something else after the last '?'. Give up.
    return false;
  }
  // Now skip backwards to the first character before the (last) block of '?'
  // signs. For 'FOO???', this would point at the second 'O'.
  size_t pre_question = hdr_.find_last_not_of('?', last_question);
  if (pre_question == std::string::npos) {
    // We can't find anything. Disallow the pattern.
    return false;
  }
  size_t prefix_len = pre_question + 1;

  // If we get here then prefix_len is the length of the prefix that we want to
  // test against. Writing this as a regex, hdr_ matches '(.*)?+$' and
  // prefix_len is the length of the capture group.
  return hdr_.compare(0, prefix_len, other.get_header(), 0, prefix_len) == 0;
}
