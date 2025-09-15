// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence disable flash access while a page write or erase is on going.
// Flash access is disabled by issuing host read intg error (a standard fault).
// After flash access is disabled, send a few random ctrl transactions
// to check those transactions are handled properly.
class flash_ctrl_access_after_disable_vseq extends flash_ctrl_otf_base_vseq;
  `uvm_object_utils(flash_ctrl_access_after_disable_vseq)
  `uvm_object_new

  constraint op_partition_c {rand_op.partition == FlashPartData;}

  virtual task body();
    flash_op_t ctrl;
    int bank, num;
    // Enable ecc for all regions
    flash_otf_region_cfg(.scr_mode(scr_ecc_cfg), .ecc_mode(OTFCfgTrue));

    `DV_CHECK(try_create_prog_op(ctrl, bank, num), "Could not create a prog flash op")
    set_otf_exp_alert("recov_err");
    prog_flash(.flash_op(ctrl), .bank(bank), .num(1), .in_err(1));
    set_local_escalation();
    flash_access_after_disabled();
  endtask // body

  // Issue host read intg error
  task set_local_escalation();
    flash_op_t host;
    bit [TL_AW-1:0] tl_addr;
    bit             saw_err, completed;
    data_4s_t rdata;
    tl_intg_err_e intg_err;

    $assertoff(0, "tb.dut.u_flash_mp.NoReqWhenErr_A");
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(intg_err,
                                       intg_err != TlIntgErrNone;)
    `uvm_info(`gfn, $sformatf("set intg_err = %s", intg_err.name), UVM_MEDIUM)
    tl_addr[OTFHostId-2:0] = $urandom();
    tl_addr[OTFBankId] = $urandom_range(0, 1);

    cfg.scb_h.exp_tl_rsp_intg_err = 1;
    cfg.scb_h.expected_alert["fatal_std_err"].expected = 1;
    cfg.scb_h.expected_alert["fatal_std_err"].max_delay = 2000;
    cfg.scb_h.exp_alert_contd["fatal_std_err"] = 10000;

    // fatal_err.phy_storage_err
    tl_access_w_abort(
                      .addr(tl_addr), .write(1'b0), .completed(completed),
                      .saw_err(saw_err),
                      .tl_access_timeout_ns(cfg.seq_cfg.erase_timeout_ns),
                      .data(rdata), .check_rsp(1'b0), .blocking(1),
                      .tl_intg_err_type(intg_err),
                      .tl_sequencer_h(p_sequencer.tl_sequencer_hs[cfg.flash_ral_name]));

    csr_utils_pkg::wait_no_outstanding_access();
    `DV_CHECK_EQ(saw_err, 1)
    csr_rd_check(.ptr(ral.std_fault_status.reg_intg_err), .compare_value(1));
    `uvm_info(`gfn, "Wait until all drain", UVM_LOW)
    cfg.clk_rst_vif.wait_clks(10);
  endtask // set_local_escalation
endclass // flash_ctrl_access_after_disable_vseq
