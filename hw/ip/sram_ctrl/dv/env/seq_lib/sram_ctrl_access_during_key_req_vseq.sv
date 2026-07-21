// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence drives memory accesses during a request to OTP for a new scrambling key,
// and verifies that accesses performed during this time are dropped (handled in scoreboard).
class sram_ctrl_access_during_key_req_vseq extends sram_ctrl_multiple_keys_vseq;

  `uvm_object_utils(sram_ctrl_access_during_key_req_vseq)
  `uvm_object_new

  virtual task pre_start();
    access_during_key_req = 1;
    // Configure the SRAM TLUL agent to wait at least 2 cycles before dropping a request for
    // non-power-of-2 SRAM sizes. This is needed in such configurations because:
    // - accesses to the unimplemented address range generate an error without being forwarded
    //   to the memory, and
    // - if the memory isn't ready (e.g. because of requesting a new scrambling key), the request
    //   is only accepted with a delay of one clock cycle (this is done to decouple a_ready from
    //   the remaining A channel signals to optimize timing, see tlul_adapter_sram.sv).
    // Without this, the DUT can signal out-of-range errors for requests which actually fall into
    // the implemented range.
    if (!$onehot(MemDepth)) begin
      cfg.m_tl_agent_cfgs[cfg.sram_ral_name].a_valid_len_min = 2;
    end
    super.pre_start();
  endtask

endclass
