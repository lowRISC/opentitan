// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Test recoverable alerts with invalid mubi data type inputs and cs_bus_cmp_alert

class csrng_alert_vseq extends csrng_base_vseq;
  `uvm_object_utils(csrng_alert_vseq)

  `uvm_object_new

  bit [31:0]      exp_recov_alert_sts;
  csrng_item      cs_item;

  task body();
    int           first_index;
    string        reg_name;
    string        fld_name;
    uvm_reg       csr;
    uvm_reg_field fld;

     `uvm_info(`gfn, $sformatf("Testing enable_field_alert"), UVM_MEDIUM)

    // Initiate with invalid mubi data
    csrng_init();

    // Wait for the recoverable alert.
    `uvm_info(`gfn, $sformatf("Waiting for alert ack to complete"), UVM_MEDIUM)
    cfg.m_alert_agent_cfg["recov_alert"].vif.wait_ack_complete();

    `uvm_info(`gfn, $sformatf("Checking RECOV_ALERT_STS register"), UVM_MEDIUM)
    reg_name = "recov_alert_sts";
    fld_name = cfg.which_invalid_mubi.name();

    first_index = find_index("_", fld_name, "first");
    csr = ral.get_reg_by_name(reg_name);
    fld = csr.get_field_by_name({fld_name.substr(first_index+1, fld_name.len()-1), "_field_alert"});

    exp_recov_alert_sts = 32'b0;
    exp_recov_alert_sts[fld.get_lsb_pos()] = 1;
    csr_rd_check(.ptr(ral.recov_alert_sts), .compare_value(exp_recov_alert_sts));

    cfg.clk_rst_vif.wait_clks(100);

    // Write valid values
    ral.ctrl.enable.set(prim_mubi_pkg::MuBi4True);
    ral.ctrl.sw_app_enable.set(prim_mubi_pkg::MuBi4True);
    ral.ctrl.read_int_state.set(prim_mubi_pkg::MuBi4True);
    csr_update(.csr(ral.ctrl));

    // Clear recov_alert_sts register
    csr_wr(.ptr(ral.recov_alert_sts), .value(32'b0));

    cfg.clk_rst_vif.wait_clks(100);

    // Check recov_alert_sts register
    csr_rd_check(.ptr(ral.recov_alert_sts), .compare_value(0));

     `uvm_info(`gfn, $sformatf("Testing cs_bus_cmp_alert"), UVM_MEDIUM)

    // Wait for CSRNG cmd_rdy
    csr_spinwait(.ptr(ral.sw_cmd_sts.cmd_rdy), .exp_data(1'b1));

    cs_item = csrng_item::type_id::create("cs_item");

    // Here we force CSRNG to generate two identical outputs to trigger a cs_bus_cmp_alert
    // Write CSRNG Cmd_Req - Instantiate Command
    cs_item.acmd  = csrng_pkg::INS;
    cs_item.clen  = 'h0;
    cs_item.flags = MuBi4True;
    cs_item.glen  = 'h0;
    `uvm_info(`gfn, $sformatf("%s", cs_item.convert2string()), UVM_DEBUG)
    send_cmd_req(SW_APP, cs_item);

    // Write CSRNG Cmd_Req Register - Generate Command
    cs_item.acmd  = csrng_pkg::GEN;
    cs_item.clen  = 'h0;
    cs_item.flags = MuBi4True;
    cs_item.glen  = 'h1;
    `uvm_info(`gfn, $sformatf("%s", cs_item.convert2string()), UVM_DEBUG)
    send_cmd_req(SW_APP, cs_item);

    // Write CSRNG Cmd_Req - Instantiate Command
    cs_item.acmd  = csrng_pkg::INS;
    cs_item.clen  = 'h0;
    cs_item.flags = MuBi4True;
    cs_item.glen  = 'h0;
    `uvm_info(`gfn, $sformatf("%s", cs_item.convert2string()), UVM_DEBUG)
    send_cmd_req(SW_APP, cs_item);

    // Write CSRNG Cmd_Req Register - Generate Command
    cs_item.acmd  = csrng_pkg::GEN;
    cs_item.clen  = 'h0;
    cs_item.flags = MuBi4True;
    cs_item.glen  = 'h1;
    `uvm_info(`gfn, $sformatf("%s", cs_item.convert2string()), UVM_DEBUG)
    send_cmd_req(SW_APP, cs_item);

    `uvm_info(`gfn, $sformatf("Waiting for alert ack to complete"), UVM_MEDIUM)
    cfg.m_alert_agent_cfg["recov_alert"].vif.wait_ack_complete();

    `uvm_info(`gfn, $sformatf("Checking RECOV_ALERT_STS register"), UVM_MEDIUM)
    exp_recov_alert_sts = 32'b0;
    exp_recov_alert_sts[ral.recov_alert_sts.cs_bus_cmp_alert.get_lsb_pos()] = 1;
    csr_rd_check(.ptr(ral.recov_alert_sts), .compare_value(exp_recov_alert_sts));

    // Clear recov_alert_sts register
    csr_wr(.ptr(ral.recov_alert_sts), .value(32'b0));

    cfg.clk_rst_vif.wait_clks(100);

    // Check recov_alert_sts register
    csr_rd_check(.ptr(ral.recov_alert_sts), .compare_value(0));

    // Turn assertions back on
    cfg.csrng_assert_vif.assert_on_alert();
  endtask : body

endclass : csrng_alert_vseq
