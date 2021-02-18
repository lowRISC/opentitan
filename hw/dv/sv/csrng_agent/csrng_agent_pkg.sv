// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package csrng_agent_pkg;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import dv_lib_pkg::*;
  import push_pull_agent_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters

  // package sources
  `include "csrng_item.sv"
  `include "csrng_agent_cfg.sv"
  `include "csrng_sequencer.sv"
  `include "csrng_agent_cov.sv"
  `include "csrng_driver.sv"
  `include "csrng_host_driver.sv"
  `include "csrng_device_driver.sv"
  `include "csrng_monitor.sv"
  `include "csrng_agent.sv"

endpackage
