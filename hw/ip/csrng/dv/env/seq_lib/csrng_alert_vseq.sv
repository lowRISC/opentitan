// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Test recoverable alerts with invalid mubi data type inputs and cs_bus_cmp_alert

class csrng_alert_vseq extends csrng_base_vseq;
  `uvm_object_utils(csrng_alert_vseq)

  `uvm_object_new

  bit [31:0]  exp_recov_alert_sts;
  csrng_item  cs_item;
  rand bit    flag0_flip_ins_cmd;
  rand acmd_e illegal_command;
  rand [3:0]  clen;
  rand [11:0] glen;

  task body();
    int           first_index;
    string        reg_name;
    string        fld_name;
    uvm_reg       csr;
    uvm_reg_field fld;

    // Values for the cs_main_sm_alert test.
    `DV_CHECK_MEMBER_RANDOMIZE_WITH_FATAL(illegal_command, illegal_command inside {INV, GENB,
                                                                                   GENU};)
    // For clen we just care about 0, 1 and the max value (coverage).
    `DV_CHECK_MEMBER_RANDOMIZE_WITH_FATAL(clen, clen inside {0, 1, 11};)

    // For glen we just care about 0, 1, 5, 9 and 13 at the moment.
    `DV_CHECK_MEMBER_RANDOMIZE_WITH_FATAL(glen, glen inside {0, 1, 5, 9, 13};)

    super.body();

    // Create EDN host sequences.
    for (int i = 0; i < NUM_HW_APPS; i++) begin
      m_edn_push_seq[i] = push_pull_host_seq#(csrng_pkg::CSRNG_CMD_WIDTH)::type_id::create
                                              ($sformatf("m_edn_push_seq[%0d]", i));
    end

    `uvm_info(`gfn, $sformatf("Testing [enable/sw_app_enable/read_int_state]_field_alert"),
        UVM_MEDIUM)

    // Initiate with invalid mubi data.
    csrng_init();

    // Wait for the recoverable alert.
    `uvm_info(`gfn, $sformatf("Waiting for alert ack to complete"), UVM_MEDIUM)
    cfg.m_alert_agent_cfgs["recov_alert"].vif.wait_ack_complete();

    `uvm_info(`gfn, $sformatf("Checking RECOV_ALERT_STS register"), UVM_MEDIUM)
    reg_name = "recov_alert_sts";
    fld_name = cfg.which_invalid_mubi.name();

    first_index = find_index("_", fld_name, "first");
    csr = ral.get_reg_by_name(reg_name);
    fld = csr.get_field_by_name({fld_name.substr(first_index+1, fld_name.len()-1), "_field_alert"});

    exp_recov_alert_sts = 32'b0;
    exp_recov_alert_sts[fld.get_lsb_pos()] = 1;
    csr_rd_check(.ptr(ral.recov_alert_sts), .compare_value(exp_recov_alert_sts));
    // Since we already did a backdoor check, sampling with this value is sufficient.
    cov_vif.cg_recov_alert_sample(.recov_alert(exp_recov_alert_sts));

    cfg.clk_rst_vif.wait_clks(100);

    // Write valid values
    ral.ctrl.enable.set(prim_mubi_pkg::MuBi4True);
    ral.ctrl.sw_app_enable.set(prim_mubi_pkg::MuBi4True);
    ral.ctrl.read_int_state.set(prim_mubi_pkg::MuBi4True);
    csr_update(.csr(ral.ctrl));

    // Clear recov_alert_sts register.
    csr_wr(.ptr(ral.recov_alert_sts), .value(32'b0));

    cfg.clk_rst_vif.wait_clks(100);

    // Check recov_alert_sts register has cleared.
    csr_rd_check(.ptr(ral.recov_alert_sts), .compare_value(0));

    `uvm_info(`gfn, $sformatf("Testing acmd_flag0_field_alert on app interface %d for %s command",
        cfg.which_app_err_alert, flag0_flip_ins_cmd ? "INS" : "RES"), UVM_MEDIUM)

    cs_item = csrng_item::type_id::create("cs_item");

    // We run some CSRNG commands and either provide an invalid encoding for the FLAG0 field of an
    // Instantiate or a Reseed command.
    // Instantiate Command.
    cs_item.acmd  = csrng_pkg::INS;
    cs_item.clen  = 'h0;
    cs_item.flags = flag0_flip_ins_cmd ?
        get_rand_mubi4_val(.t_weight(0), .f_weight(0), .other_weight(1)) : MuBi4True;
    cs_item.glen  = 'h0;
    `uvm_info(`gfn, $sformatf("%s", cs_item.convert2string()), UVM_DEBUG)
    send_cmd_req(cfg.which_app_err_alert, cs_item, .edn_rst_as_ack(0));

    // Reseed Command.
    cs_item.acmd  = csrng_pkg::RES;
    cs_item.clen  = 'h0;
    cs_item.flags = !flag0_flip_ins_cmd ?
        get_rand_mubi4_val(.t_weight(0), .f_weight(0), .other_weight(1)) : MuBi4True;
    cs_item.glen  = 'h1;
    `uvm_info(`gfn, $sformatf("%s", cs_item.convert2string()), UVM_DEBUG)
    send_cmd_req(cfg.which_app_err_alert, cs_item, .edn_rst_as_ack(0));

    if (!flag0_flip_ins_cmd) begin
      // The previous command interpreting flag0 detected an invalid MuBi encoding. We need
      // to run another command with a valid MuBi encoded flag0 to clear the previous
      // value internally. Otherwise the corresponding RECOV_ALERT_STS status bit keeps getting
      // asserted.
      cs_item.acmd  = csrng_pkg::RES;
      cs_item.clen  = 'h0;
      cs_item.flags = MuBi4True;
      cs_item.glen  = 'h1;
      `uvm_info(`gfn, $sformatf("%s", cs_item.convert2string()), UVM_DEBUG)
      send_cmd_req(cfg.which_app_err_alert, cs_item, .edn_rst_as_ack(0));
    end

    `uvm_info(`gfn, $sformatf("Waiting for alert ack to complete"), UVM_MEDIUM)
    cfg.m_alert_agent_cfgs["recov_alert"].vif.wait_ack_complete();

    `uvm_info(`gfn, $sformatf("Checking RECOV_ALERT_STS register"), UVM_MEDIUM)
    exp_recov_alert_sts = 32'b0;
    exp_recov_alert_sts[ral.recov_alert_sts.acmd_flag0_field_alert.get_lsb_pos()] = 1;
    csr_rd_check(.ptr(ral.recov_alert_sts), .compare_value(exp_recov_alert_sts));
    // Since we already did a backdoor check, sampling with this value is sufficient.
    cov_vif.cg_recov_alert_sample(.recov_alert(exp_recov_alert_sts));

    // Clear recov_alert_sts register.
    csr_wr(.ptr(ral.recov_alert_sts), .value(32'b0));

    cfg.clk_rst_vif.wait_clks(100);

    // Check recov_alert_sts register has cleared.
    csr_rd_check(.ptr(ral.recov_alert_sts), .compare_value(0));

    `uvm_info(`gfn, $sformatf("Testing cs_bus_cmp_alert"), UVM_MEDIUM)

    // Here we force CSRNG to generate two identical outputs to trigger a cs_bus_cmp_alert.
    // Write CSRNG Cmd_Req - Instantiate Command.
    cs_item.acmd  = csrng_pkg::INS;
    cs_item.clen  = 'h0;
    cs_item.flags = MuBi4True;
    cs_item.glen  = 'h0;
    `uvm_info(`gfn, $sformatf("%s", cs_item.convert2string()), UVM_DEBUG)
    send_cmd_req(SW_APP, cs_item);

    // Write CSRNG Cmd_Req Register - Generate Command.
    cs_item.acmd  = csrng_pkg::GEN;
    cs_item.clen  = 'h0;
    cs_item.flags = MuBi4True;
    cs_item.glen  = 'h1;
    `uvm_info(`gfn, $sformatf("%s", cs_item.convert2string()), UVM_DEBUG)
    send_cmd_req(SW_APP, cs_item);

    // Write CSRNG Cmd_Req - Instantiate Command.
    cs_item.acmd  = csrng_pkg::INS;
    cs_item.clen  = 'h0;
    cs_item.flags = MuBi4True;
    cs_item.glen  = 'h0;
    `uvm_info(`gfn, $sformatf("%s", cs_item.convert2string()), UVM_DEBUG)
    send_cmd_req(SW_APP, cs_item);

    // Write CSRNG Cmd_Req Register - Generate Command.
    cs_item.acmd  = csrng_pkg::GEN;
    cs_item.clen  = 'h0;
    cs_item.flags = MuBi4True;
    cs_item.glen  = 'h1;
    `uvm_info(`gfn, $sformatf("%s", cs_item.convert2string()), UVM_DEBUG)
    send_cmd_req(SW_APP, cs_item);

    `uvm_info(`gfn, $sformatf("Waiting for alert ack to complete"), UVM_MEDIUM)
    cfg.m_alert_agent_cfgs["recov_alert"].vif.wait_ack_complete();

    `uvm_info(`gfn, $sformatf("Checking RECOV_ALERT_STS register"), UVM_MEDIUM)
    exp_recov_alert_sts = 32'b0;
    exp_recov_alert_sts[ral.recov_alert_sts.cs_bus_cmp_alert.get_lsb_pos()] = 1;
    csr_rd_check(.ptr(ral.recov_alert_sts), .compare_value(exp_recov_alert_sts));
    // Since we already did a backdoor check, sampling with this value is sufficient.
    cov_vif.cg_recov_alert_sample(.recov_alert(exp_recov_alert_sts));

    // Clear recov_alert_sts register.
    csr_wr(.ptr(ral.recov_alert_sts), .value(32'b0));

    cfg.clk_rst_vif.wait_clks(100);

    // Check recov_alert_sts register has cleared.
    csr_rd_check(.ptr(ral.recov_alert_sts), .compare_value(0));

    `uvm_info(`gfn, $sformatf("Testing cs_main_sm_alert for app %d", cfg.which_app_err_alert), UVM_MEDIUM)

    // Here we send an illegal command to CSRNG to check that cs_main_sm_alert is triggered.
    // Sending an illegal command does not get a response from CSRNG.
    cs_item.acmd  = illegal_command;
    cs_item.clen  = clen;
    cs_item.flags = get_rand_mubi4_val(.t_weight(4), .f_weight(4), .other_weight(0));
    cs_item.glen  = glen;
    send_cmd_req(cfg.which_app_err_alert, cs_item, .await_response(1'b0));

    `uvm_info(`gfn, $sformatf("Waiting for alert ack to complete"), UVM_MEDIUM)
    cfg.m_alert_agent_cfgs["recov_alert"].vif.wait_ack_complete();

    `uvm_info(`gfn, $sformatf("Checking RECOV_ALERT_STS register"), UVM_MEDIUM)
    exp_recov_alert_sts = 32'b0;
    exp_recov_alert_sts[ral.recov_alert_sts.cs_main_sm_alert.get_lsb_pos()] = 1;
    csr_spinwait(.ptr(ral.recov_alert_sts), .exp_data(exp_recov_alert_sts));
    // Since we already did a backdoor check, sampling with this value is sufficient.
    cov_vif.cg_recov_alert_sample(.recov_alert(exp_recov_alert_sts));

    `uvm_info(`gfn, $sformatf("Checking RECOV_ALERT_STS reset"), UVM_MEDIUM)
    // Toggle enable to put main FSM back into legal state.
    ral.ctrl.enable.set(prim_mubi_pkg::MuBi4False);
    csr_update(.csr(ral.ctrl));
    cfg.clk_rst_vif.wait_clks(100);
    ral.ctrl.enable.set(prim_mubi_pkg::MuBi4True);
    csr_update(.csr(ral.ctrl));

    // The uninstantiate is not really needed. At the moment, it's mainly useful for coverage.
    cs_item.acmd  = csrng_pkg::UNI;
    cs_item.clen  = clen;
    cs_item.flags = get_rand_mubi4_val(.t_weight(4), .f_weight(4), .other_weight(0));
    cs_item.glen  = glen;
    send_cmd_req(cfg.which_app_err_alert, cs_item, .await_response(1'b1));

    // Clear recov_alert_sts register.
    csr_wr(.ptr(ral.recov_alert_sts), .value(32'b0));
    cfg.clk_rst_vif.wait_clks(100);
    // Check recov_alert_sts register has cleared.
    csr_rd_check(.ptr(ral.recov_alert_sts), .compare_value(0));

    // Turn assertions back on.
    cfg.csrng_assert_vif.assert_on_alert();
  endtask : body

endclass : csrng_alert_vseq
