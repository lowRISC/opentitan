// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#ifndef OPENTITAN_HW_IP_OTBN_DV_MODEL_OTBN_TRACE_ENTRY_H_
#define OPENTITAN_HW_IP_OTBN_DV_MODEL_OTBN_TRACE_ENTRY_H_

#include <string>
#include <vector>

class OtbnTraceEntry {
 public:
  virtual ~OtbnTraceEntry(){};

  void from_rtl_trace(const std::string &trace);

  void print(const std::string &indent, std::ostream &os) const;

  void take_writes(const OtbnTraceEntry &other);

  // True if the entry is empty (no header or other text)
  bool empty() const;

  // True if this is a stall
  bool is_stall() const;

  // True if this is an execute line
  bool is_exec() const;

  // True if this is an acceptable line to follow other (assumed to
  // have been a stall)
  bool is_compatible(const OtbnTraceEntry &other) const;

  const std::string &get_header() const { return hdr_; }
  const std::vector<std::string> &get_writes() const { return writes_; }

 protected:
  std::string hdr_;
  std::vector<std::string> writes_;
};

class OtbnIssTraceEntry : public OtbnTraceEntry {
 public:
  bool from_iss_trace(const std::vector<std::string> &lines);

  // Return true if this ISS trace entry is a valid model of other.
  // This is true if the entries match exactly (of course!), but also
  // allows a bit more wiggle room with some ISS entries that might
  // not specify some fields exactly.
  bool is_model_of(const OtbnTraceEntry &other) const;

  // Fields that are populated from the "special" line for ISS entries
  struct IssData {
    uint32_t insn_addr;
    std::string mnemonic;
  };

  IssData data_;
};

#endif  // OPENTITAN_HW_IP_OTBN_DV_MODEL_OTBN_TRACE_ENTRY_H_
