// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class pattgen_host_driver extends pattgen_driver;
  `uvm_component_utils(pattgen_host_driver)
  `uvm_component_new

  // pattgen_agent is only operating in device mode
endclass : pattgen_host_driver
