// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#pragma once

#include <vector>

#include "otbn_trace_listener.h"

// A source for simulation trace data.
//
// This is a singleton class, which will be constructed on the first call to
// get() or the first trace data that comes back from the simulation.
//
// The object is in charge of taking trace data from the simulation (which is
// sent by calling the accept_otbn_trace_string DPI function) and passing it
// out to registered listeners.

class OtbnTraceSource {
 public:
  // Get the (singleton) OtbnTraceSource object
  static OtbnTraceSource &get();

  // Add a listener to the source
  void AddListener(OtbnTraceListener *listener);

  // Remove a listener from the source
  void RemoveListener(const OtbnTraceListener *listener);

  // Send a trace string to all listeners
  void Broadcast(const std::string &trace, unsigned cycle_count);

 private:
  std::vector<OtbnTraceListener *> listeners_;
};
