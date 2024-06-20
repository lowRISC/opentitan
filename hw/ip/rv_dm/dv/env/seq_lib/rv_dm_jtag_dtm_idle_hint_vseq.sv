// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//rv_dm_jtag_dtm_idle_hint
class rv_dm_jtag_dtm_idle_hint_vseq  extends rv_dm_base_vseq;
  `uvm_object_utils(rv_dm_jtag_dtm_idle_hint_vseq)
  `uvm_object_new

  // Read the dtmcs register and check the idle field has the expected value.
  task check_idle(bit [2:0] expected_idle);
    uvm_reg_data_t rdata;
    csr_rd(.ptr(jtag_dtm_ral.dtmcs), .value(rdata));
    `DV_CHECK_EQ(expected_idle, get_field_val(jtag_dtm_ral.dtmcs.idle, rdata))
  endtask

  // Read the dtmcs register and check the dmistat field has the expected value.
  task check_dmistat(bit [1:0] expected_dmistat);
    uvm_reg_data_t rdata;
    csr_rd(.ptr(jtag_dtm_ral.dtmcs), .value(rdata));
    `DV_CHECK_EQ(expected_dmistat, get_field_val(jtag_dtm_ral.dtmcs.dmistat, rdata))
  endtask

  task body();
    uvm_reg_data_t rdata;

    // We expect dtmcs.idle to have value 1, which means that a debugger (user of the debug module)
    // can avoid a busy dmistat by entering run-test/idle and leaving it immediately.
    check_idle(3'h1);

    // Tell the JTAG agent to act on this idle value. Setting the min_rti knob bypasses a 1-cycle
    // minimum delay in run-test/idle that we'd get from the JTAG driver otherwise.
    cfg.m_jtag_agent_cfg.min_rti = 1;

    // Write some arbitrary data words over DMI
    csr_wr(.ptr(jtag_dmi_ral.abstractdata[0]), .value(32'h0d158c94));
    csr_wr(.ptr(jtag_dmi_ral.progbuf[0]), .value(32'h0d000c84));
    csr_wr(.ptr(jtag_dmi_ral.command), .value(32'h0d000c84));

    // Read dtmcs back again and check that dmistat is zero (no error)
    check_dmistat(2'h0);
  endtask

endclass : rv_dm_jtag_dtm_idle_hint_vseq
