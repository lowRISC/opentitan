// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "otbn_trace_checker.h"

#include <cassert>
#include <cstring>
#include <iostream>
#include <memory>

#include "otbn_trace_source.h"
#include "sv_utils.h"

static std::unique_ptr<OtbnTraceChecker> trace_checker;

OtbnTraceChecker::OtbnTraceChecker()
    : rtl_started_(false),
      rtl_pending_(false),
      iss_started_(false),
      iss_pending_(false),
      done_(true),
      seen_err_(false),
      last_data_vld_(false) {
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
  OtbnTraceEntry trace_entry;
  if (!trace_entry.from_rtl_trace(trace)) {
    seen_err_ = true;
    return;
  }
  if (trace_entry.trace_type() == OtbnTraceEntry::Invalid) {
    std::cerr << "ERROR: Invalid RTL trace entry with invalid header:\n";
    trace_entry.print("  ", std::cerr);
    seen_err_ = true;
    return;
  }

  // Check we don't already have a pending RTL final entry
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

  // At this point, we know that the header is a Stall, Exec, WipeInProgress or
  // WipeComplete. We want to coalesce entries for an instruction/wipe here to
  // avoid the ISS needing to figure out which write happens at what time on a
  // multi-cycle instruction.
  //
  // We work on the basis that an instruction will appear as zero or more
  // "partial entries" (S or U) followed by an "final" entry (E or V). When we
  // see a partial entry, we merge it into rtl_partial_entry_, setting
  // rtl_partial_ to flag that it contains some information.
  //
  // When a final entry comes up, we check it matches any pending partial entry
  // and then merge all the fields together, finally setting rtl_pending_.
  if (trace_entry.is_partial()) {
    if (rtl_started_) {
      // We already have a partial entry. Make sure the headers match.
      if (!trace_entry.is_compatible(rtl_entry_)) {
        std::cerr
            << ("ERROR: Partial trace entry followed by "
                "mis-matching partial entry.\n"
                "  Existing partial entry was:\n");
        rtl_entry_.print("    ", std::cerr);
        std::cerr << "  New partial entry was:\n";
        trace_entry.print("    ", std::cerr);
        seen_err_ = true;
        return;
      }
      rtl_entry_.take_writes(trace_entry, false);
    } else {
      // This is the first partial entry. Set the rtl_started_ flag and save
      // trace_entry.
      rtl_started_ = true;
      rtl_entry_ = trace_entry;
    }
    return;
  }

  // This wasn't a partial entry. At this point, we should know it's a final
  // one.
  assert(trace_entry.is_final());

  // If had a partial entry before, merge in any writes from it, making sure
  // the entries are compatible.
  if (rtl_started_) {
    if (!trace_entry.is_compatible(rtl_entry_)) {
      std::cerr
          << ("ERROR: Final trace entry doesn't match partial entry:\n"
              "  Partial entry was:\n");
      rtl_entry_.print("    ", std::cerr);
      std::cerr << "  Final entry was:\n";
      trace_entry.print("    ", std::cerr);
      seen_err_ = true;
      return;
    }

    trace_entry.take_writes(rtl_entry_, true);
  }

  rtl_pending_ = true;
  rtl_started_ = false;
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

  OtbnIssTraceEntry trace_entry;
  if (!trace_entry.from_iss_trace(lines)) {
    // Error parsing ISS trace. This has already printed a message to stderr.
    // Just return false to pass the error code along.
    return false;
  }

  done_ = false;

  if (iss_pending_) {
    // An instruction finished execution on the ISS and its trace entry is
    // stored in iss_entry_. Another one has just started, but we haven't
    // seen an RTL trace entry in the intervening time.
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

  if (iss_started_) {
    // We have some changes associated with a stall. Merge in the changes that
    // we've just seen. We do it "backwards" so that if trace_entry is an
    // final entry then so is the result.
    trace_entry.take_writes(iss_entry_, true);
  }

  iss_started_ = true;
  iss_entry_ = trace_entry;

  // Set the pending flag if we've got the end of an event (either E or V).
  if (iss_entry_.is_final()) {
    iss_pending_ = true;
  }

  return MatchPair();
}

void OtbnTraceChecker::Flush() {
  rtl_pending_ = false;
  rtl_started_ = false;
  iss_pending_ = false;
  iss_started_ = false;
  no_sec_wipe_data_chk_ = false;
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

const OtbnIssTraceEntry::IssData *OtbnTraceChecker::PopIssData() {
  if (!last_data_vld_)
    return nullptr;

  last_data_vld_ = false;
  return &last_data_;
}

void OtbnTraceChecker::set_no_sec_wipe_chk() { no_sec_wipe_data_chk_ = true; }

bool OtbnTraceChecker::MatchPair() {
  if (!(rtl_pending_ && iss_pending_)) {
    return true;
  }
  rtl_pending_ = false;
  iss_pending_ = false;
  iss_started_ = false;
  if (!(rtl_entry_.compare_rtl_iss_entries(iss_entry_,
                                           no_sec_wipe_data_chk_))) {
    std::cerr
        << ("ERROR: Mismatch between RTL and ISS trace entries.\n"
            "  RTL entry is:\n");
    rtl_entry_.print("    ", std::cerr);
    std::cerr << "  ISS entry is:\n";
    iss_entry_.print("    ", std::cerr);
    seen_err_ = true;
    return false;
    if (rtl_entry_.trace_type() == OtbnTraceEntry::WipeComplete) {
      no_sec_wipe_data_chk_ = false;
    }
  }
  // We've got a matching pair of entries. Move the ISS data out of the (now
  // defunct) iss_entry_ and into last_data_.
  if (rtl_entry_.trace_type() == OtbnTraceEntry::Exec) {
    last_data_ = std::move(iss_entry_.data_);
    last_data_vld_ = true;
  }

  return true;
}

// Exposed over DPI as:
//
//  import "DPI-C" function bit
//    otbn_trace_checker_pop_iss_insn(output bit [31:0] insn_addr,
//                                    output string     mnemonic);
//
// Any string output argument will stay unchanged until the next call to this
// function.

extern "C" unsigned char otbn_trace_checker_pop_iss_insn(
    svBitVecVal *insn_addr, const char **mnemonic) {
  static char mnemonic_buf[16];

  const OtbnIssTraceEntry::IssData *iss_data =
      OtbnTraceChecker::get().PopIssData();
  if (!iss_data)
    return 0;

  assert(iss_data->mnemonic.size() + 1 <= sizeof mnemonic_buf);
  memcpy(mnemonic_buf, iss_data->mnemonic.c_str(),
         iss_data->mnemonic.size() + 1);
  *mnemonic = mnemonic_buf;

  set_sv_u32(insn_addr, iss_data->insn_addr);

  return 1;
}
