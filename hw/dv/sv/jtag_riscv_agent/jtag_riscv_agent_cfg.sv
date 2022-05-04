// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class jtag_riscv_agent_cfg extends dv_base_agent_cfg;
  `uvm_object_utils_begin(jtag_riscv_agent_cfg)
  `uvm_object_utils_end

  jtag_agent_cfg m_jtag_agent_cfg;
  jtag_sequencer jtag_sequencer_h;

  // Allows JTAG to return error status.
  bit allow_errors = 0;

  // RV_DM jtag connects to DM CSRs.
  // Because LC jtag will normalize the input address for the last two bits,
  // while RV_DM jtag uses the original DM CSR addresses without the normalization.
  bit is_rv_dm = 0;

  // Indicates the rv_dm jtag is activated or not. Only valid when is_rv_dm = 1.
  // It can be only updated by driver and sequence shouldn't set this variable.
  bit rv_dm_activated = 0;

  // Allows activation to fail. Only valid when is_rv_dm = 1.
  bit allow_rv_dm_activation_fail = 0;

  // Max attempts to activate rv_dm.
  int max_rv_dm_activation_attempts = 100;

  // status to return if we assert in_reset
  logic [DMI_OPW-1:0] status_in_reset;

  function new(string name = "");
    super.new(name);
    // Default active
    has_driver      = 1;
    status_in_reset = DmiNoErr;
  endfunction : new

endclass
