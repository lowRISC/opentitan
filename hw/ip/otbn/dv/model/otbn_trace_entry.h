// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#ifndef OPENTITAN_HW_IP_OTBN_DV_MODEL_OTBN_TRACE_ENTRY_H_
#define OPENTITAN_HW_IP_OTBN_DV_MODEL_OTBN_TRACE_ENTRY_H_

#include <string>
#include <vector>

class OtbnTraceEntry {
 public:
  enum trace_type_t {
    Invalid,
    Stall,
    Exec,
    WipeInProgress,
    WipeComplete,
  };

  virtual ~OtbnTraceEntry(){};

  void from_rtl_trace(const std::string &trace);

  bool operator==(const OtbnTraceEntry &other) const;
  void print(const std::string &indent, std::ostream &os) const;

  void take_writes(const OtbnTraceEntry &other);

  trace_type_t trace_type() const { return trace_type_; }

  // True if this is an acceptable line to follow other (assumed to
  // have been of type Stall or WipeInProgress)
  bool is_compatible(const OtbnTraceEntry &other) const;

  // True if this entry is "partial" (Stall or WipeInProgress)
  bool is_partial() const;

  // True if this entry is "final" (Exec or WipeComplete)
  bool is_final() const;

 protected:
  static trace_type_t hdr_to_trace_type(const std::string &hdr);

  trace_type_t trace_type_;
  std::string hdr_;
  std::vector<std::string> writes_;
};

class OtbnIssTraceEntry : public OtbnTraceEntry {
 public:
  bool from_iss_trace(const std::vector<std::string> &lines);

  // Fields that are populated from the "special" line for ISS entries
  struct IssData {
    uint32_t insn_addr;
    std::string mnemonic;
  };

  IssData data_;
};

#endif  // OPENTITAN_HW_IP_OTBN_DV_MODEL_OTBN_TRACE_ENTRY_H_
