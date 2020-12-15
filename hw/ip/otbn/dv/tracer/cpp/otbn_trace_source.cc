// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "otbn_trace_source.h"

#include <algorithm>
#include <cassert>
#include <memory>

static std::unique_ptr<OtbnTraceSource> trace_source;

OtbnTraceSource &OtbnTraceSource::get() {
  if (!trace_source) {
    trace_source.reset(new OtbnTraceSource());
  }
  return *trace_source;
}

void OtbnTraceSource::AddListener(OtbnTraceListener *listener) {
  listeners_.push_back(listener);
}

void OtbnTraceSource::RemoveListener(const OtbnTraceListener *listener) {
  auto it = std::find(listeners_.begin(), listeners_.end(), listener);
  assert(it != listeners_.end());
  listeners_.erase(it);
}

void OtbnTraceSource::Broadcast(const std::string &trace,
                                unsigned cycle_count) {
  for (OtbnTraceListener *listener : listeners_) {
    listener->AcceptTraceString(trace, cycle_count);
  }
}

extern "C" void accept_otbn_trace_string(const char *trace,
                                         unsigned int cycle_count) {
  assert(trace != nullptr);
  OtbnTraceSource::get().Broadcast(trace, cycle_count);
}
