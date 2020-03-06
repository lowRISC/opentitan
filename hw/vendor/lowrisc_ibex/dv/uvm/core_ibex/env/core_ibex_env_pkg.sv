// Copyright 2018 lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// ---------------------------------------------
// Core ibex environment package
// ---------------------------------------------

`include "core_ibex_dut_probe_if.sv"
`include "core_ibex_rvfi_if.sv"
`include "core_ibex_csr_if.sv"

package core_ibex_env_pkg;

  import uvm_pkg::*;
  import ibex_mem_intf_agent_pkg::*;
  import irq_agent_pkg::*;

  `include "core_ibex_vseqr.sv"
  `include "core_ibex_env_cfg.sv"
  `include "core_ibex_env.sv"

endpackage
