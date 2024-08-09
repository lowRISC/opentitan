// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//rv_dm_jtag_dtm_idle_hint
class rv_dm_jtag_dtm_idle_hint_vseq  extends rv_dm_base_vseq;
  `uvm_object_utils(rv_dm_jtag_dtm_idle_hint_vseq)
  `uvm_object_new

  // Read the dtmcs register and check the idle field has the expected value unless the system is in
  // reset.
  task check_idle(bit [2:0] expected_idle);
    uvm_reg_data_t rdata;
    csr_rd(.ptr(jtag_dtm_ral.dtmcs), .value(rdata));
    if (cfg.clk_rst_vif.rst_n)
      `DV_CHECK_EQ(expected_idle, get_field_val(jtag_dtm_ral.dtmcs.idle, rdata))
  endtask

  task body();
    uvm_reg_data_t rdata;

    // We expect dtmcs.idle to have value 1, which means that a debugger (user of the debug module)
    // can avoid a busy dmistat by entering run-test/idle and leaving it immediately.
    check_idle(3'h1);
    if (!cfg.clk_rst_vif.rst_n) return;

    // Tell the JTAG agent to act on this idle value. Setting the min_rti knob bypasses a 1-cycle
    // minimum delay in run-test/idle that we'd get from the JTAG driver otherwise.
    cfg.m_jtag_agent_cfg.min_rti = 1;

    // Write some arbitrary data words over DMI
    repeat (4) begin
      randcase
        1: csr_wr(.ptr(jtag_dmi_ral.abstractdata[0]), .value($urandom));
        1: csr_wr(.ptr(jtag_dmi_ral.progbuf[0]), .value($urandom));
      endcase
    end

    if (!cfg.clk_rst_vif.rst_n) return;

    // Read dtmcs back again and check that dmistat is zero (no error)
    check_dmistat(2'h0);
  endtask

endclass : rv_dm_jtag_dtm_idle_hint_vseq
