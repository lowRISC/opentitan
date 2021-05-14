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

  bool operator==(const OtbnTraceEntry &other) const;
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

 protected:
  std::string hdr_;
  std::vector<std::string> writes_;
};

class OtbnIssTraceEntry : public OtbnTraceEntry {
 public:
  bool from_iss_trace(const std::vector<std::string> &lines);

  // Fields that are populated from the "special" line for ISS entries
  struct IssData {
    std::string mnemonic;
  };

  IssData data_;
};

#endif  // OPENTITAN_HW_IP_OTBN_DV_MODEL_OTBN_TRACE_ENTRY_H_
