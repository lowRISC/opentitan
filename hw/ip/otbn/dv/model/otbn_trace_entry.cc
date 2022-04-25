// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "otbn_trace_entry.h"

#include <cassert>
#include <iostream>
#include <regex>
#include <sstream>

bool OtbnTraceBodyLine::fill_from_string(const std::string &src,
                                         const std::string &line) {
  // A valid line matches the following regex
  std::regex re("(.) ([^:]+): (.+)");
  std::smatch match;

  if (!std::regex_match(line, match, re)) {
    std::cerr << "OTBN trace body line from " << src
              << " does not have expected format. Saw: `" << line << "'.\n";
    return false;
  }

  assert(match.size() == 4);

  raw_ = line;
  type_ = match[1].str()[0];
  loc_ = match[2].str();
  value_ = match[3].str();
  return true;
}

bool OtbnTraceBodyLine::operator==(const OtbnTraceBodyLine &other) const {
  return raw_ == other.raw_;
}

bool OtbnTraceEntry::from_rtl_trace(const std::string &trace) {
  size_t eol = trace.find('\n');
  hdr_ = trace.substr(0, eol);
  trace_type_ = hdr_to_trace_type(hdr_);

  while (eol != std::string::npos) {
    size_t bol = eol + 1;
    eol = trace.find('\n', bol);
    size_t line_len =
        (eol == std::string::npos) ? std::string::npos : eol - bol;
    std::string line = trace.substr(bol, line_len);

    // We're only interested in register writes
    if (!(line.size() > 0 && line[0] == '>'))
      continue;

    OtbnTraceBodyLine parsed_line;
    if (!parsed_line.fill_from_string("RTL", line)) {
      return false;
    }
    writes_[parsed_line.get_loc()].push_back(parsed_line);
  }
  return true;
}

bool OtbnTraceEntry::compare_rtl_iss_entries(const OtbnTraceEntry &other,
                                             bool no_sec_wipe_data_chk) const {
  if (hdr_ != other.hdr_)
    return false;

  for (const auto &rtlptr : writes_) {
    auto isskey = other.writes_.find(rtlptr.first);
    if (isskey == other.writes_.end())
      return false;
    // compare rtlptr.second and isskey.second
    if (!check_entries_compatible(trace_type_, rtlptr.first, rtlptr.second,
                                  isskey->second, no_sec_wipe_data_chk))
      return false;
  }

  if (writes_.size() != other.writes_.size())
    return false;
  return true;
}

bool OtbnTraceEntry::check_entries_compatible(
    trace_type_t type, const std::string &key,
    const std::vector<OtbnTraceBodyLine> &rtl_lines,
    const std::vector<OtbnTraceBodyLine> &iss_lines,
    bool no_sec_wipe_data_chk) {
  assert(rtl_lines.size() && iss_lines.size());
  assert(type == WipeComplete || type == Exec);

  if (type == WipeComplete && key != "FLAGS0" && key != "FLAGS1") {
    if (rtl_lines.size() != 2)
      return false;
    if (!no_sec_wipe_data_chk && type == WipeComplete) {
      if (rtl_lines.front() == rtl_lines.back())
        return false;
    }
  }

  return rtl_lines.back() == iss_lines.back();
}

void OtbnTraceEntry::print(const std::string &indent, std::ostream &os) const {
  os << indent << hdr_ << "\n";
  for (const auto &pr : writes_) {
    for (const auto &line : pr.second) {
      os << indent << line.get_string() << "\n";
    }
  }
}

void OtbnTraceEntry::take_writes(const OtbnTraceEntry &other,
                                 bool other_first) {
  for (const auto &pr : other.writes_) {
    std::vector<OtbnTraceBodyLine> &so_far = writes_[pr.first];
    if (other_first) {
      // If other_first is true, we should prepend the writes from other. We do
      // so by creating a temporary vector (with a copy of the writes from
      // other) and then appending any writes we had before.
      std::vector<OtbnTraceBodyLine> tmp(pr.second);
      tmp.insert(tmp.end(), so_far.begin(), so_far.end());
      writes_[pr.first] = tmp;
    } else {
      // If other_first is false, we should append the writes from other. We
      // can do that with just a call to insert.
      so_far.insert(so_far.end(), pr.second.begin(), pr.second.end());
    }
  }
}

bool OtbnTraceEntry::is_compatible(const OtbnTraceEntry &prev) const {
  // Two entries are compatible if they might both come from the multi-cycle
  // execution of one instruction. For example, you might expect to see these
  // two lines:
  //
  //   S PC: 0x00000010, insn: 0x00107db8
  //   E PC: 0x00000010, insn: 0x00107db8
  //
  // which show an instruction at 0x10 stalling for a cycle and then managing
  // to execute.
  //
  // Similarly, you might expect to see U followed by U or V.
  //
  // As an added complication, if we see an IMEM fetch error, the entry will
  // become
  //
  //   E PC: 0x00000010, insn: ??
  //
  // and that's fine. So the rule is:
  //
  //   - Check the types are compatible (S then S or E; U then U or V)
  //   - Compare the two lines from character 1 onwards.
  //   - If they match: accept.
  //   - Otherwise, if the second line has no '?' then reject.
  //   - If there is a '?' and they match up to that point, accept.
  //   - Otherwise: reject
  //
  // (This wrongly accepts some malformed examples, but that's fine: it's just
  // meant as a quick check to make sure our trace machinery isn't dropping
  // entries)
  bool matching_types;
  switch (prev.trace_type()) {
    case Stall:
      matching_types = (trace_type_ == Stall || trace_type_ == Exec);
      break;
    case WipeInProgress:
      matching_types =
          (trace_type_ == WipeInProgress || trace_type_ == WipeComplete);
      break;
    default:
      matching_types = false;
  }
  if (!matching_types)
    return false;

  bool exact_match =
      0 == hdr_.compare(1, std::string::npos, prev.hdr_, 1, std::string::npos);
  if (exact_match)
    return true;

  size_t first_qm = hdr_.find('?', 1);
  if (first_qm == std::string::npos)
    return false;

  return 0 == hdr_.compare(1, first_qm - 1, prev.hdr_, 1, first_qm - 1);
}

bool OtbnTraceEntry::is_partial() const {
  return ((trace_type_ == OtbnTraceEntry::Stall) ||
          (trace_type_ == OtbnTraceEntry::WipeInProgress));
}

bool OtbnTraceEntry::is_final() const {
  return ((trace_type_ == OtbnTraceEntry::Exec) ||
          (trace_type_ == OtbnTraceEntry::WipeComplete));
}

OtbnTraceEntry::trace_type_t OtbnTraceEntry::hdr_to_trace_type(
    const std::string &hdr) {
  if (hdr.empty()) {
    return Invalid;
  }

  switch (hdr[0]) {
    case 'S':
      return Stall;
    case 'E':
      return Exec;
    case 'U':
      return WipeInProgress;
    case 'V':
      return WipeComplete;
    default:
      return Invalid;
  }
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
        trace_type_ = hdr_to_trace_type(hdr_);
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
          OtbnTraceBodyLine parsed_line;
          if (!parsed_line.fill_from_string("ISS", line)) {
            return false;
          }
          writes_[parsed_line.get_loc()].push_back(parsed_line);
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

  return true;
}
