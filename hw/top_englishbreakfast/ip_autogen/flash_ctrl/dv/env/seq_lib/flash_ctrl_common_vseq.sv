// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class flash_ctrl_common_vseq extends flash_ctrl_otf_base_vseq;
  `uvm_object_utils(flash_ctrl_common_vseq)

  `uvm_object_new

  virtual function void configure_vseq();
    cfg.seq_cfg.max_num_trans = 2;
  endfunction

  virtual task pre_start();
    super.pre_start();
    // After reset, scoreboard need to wait until wip process is done.
    // Since common reset test is not aware of it, remove check from sb and
    // have each test check read response.
    if (common_seq_type inside {"stress_all_with_rand_reset", "csr_mem_rw_with_rand_reset"}) begin
      cfg.scb_h.skip_read_check = 1'b1;
    end
    // Remove prim from following test until alert issue is resolved
    if (common_seq_type inside {"same_csr_outstanding"}) begin
      foreach (all_csrs[i]) begin
        csr_excl_item csr_excl = get_excl_item(all_csrs[i]);
        if (!uvm_re_match("*prim_reg_block*", all_csrs[i].get_full_name)) begin
          csr_excl.add_excl(all_csrs[i].get_full_name, CsrExclAll, CsrRwTest);
        end

      end
    end else begin
      csr_excl_item csr_excl = ral.get_excl_item();
      csr_excl.add_excl("flash_ctrl_core_reg_block.init", CsrExclAll, CsrAllTests);
    end
  endtask // pre_start

  function void disable_fi_for_prim_count(string path);
    sec_cm_pkg::find_sec_cm_if_proxy(.path({path, "*u_rptr"}), .is_regex(1)).disable_fi();
    sec_cm_pkg::find_sec_cm_if_proxy(.path({path, "*u_wptr"}), .is_regex(1)).disable_fi();
  endfunction

  task dut_init(string reset_kind = "HARD");
    // Disable fault injection on the prim_count module associated with the TL-UL
    // adapter SRAM request and sramreqfifo fifo.
    //
    // This is because injecting a fault causes a spurious TL transaction whose response
    // eventually causes a fatal alert (good). Unfortunately, the FIFOs might actually have
    // been empty, so lots of signals in the design become X. This includes FLASH_CTRL's
    // bus_integ_error signal than then cannot be reliably sensed in the DV environment.
    // The code here disables fault injection at that location.
    disable_fi_for_prim_count("*u_tl_adapter_eflash*u_rspfifo*u_fifo_cnt");
    disable_fi_for_prim_count("*u_tl_adapter_eflash*u_reqfifo*u_fifo_cnt");
    disable_fi_for_prim_count("*u_tl_adapter_eflash*u_sramreqfifo*u_fifo_cnt");
    disable_fi_for_prim_count("*u_to_rd_fifo*u_reqfifo*u_fifo_cnt");
    disable_fi_for_prim_count("*u_to_rd_fifo*u_sramreqfifo*u_fifo_cnt");

    super.dut_init(reset_kind);
  endtask // dut_init

  virtual task body();
    string path[] = {
      {"tb.dut.u_eflash.gen_flash_cores[0].u_core.u_rd",
              ".u_rd_storage.gen_normal_fifo.storage_rdata[74:0]"},
      {"tb.dut.u_eflash.gen_flash_cores[1].u_core.u_rd",
              ".u_rd_storage.gen_normal_fifo.storage_rdata[74:0]"},
      "tb.dut.u_to_rd_fifo.u_rspfifo.gen_normal_fifo.storage_rdata[39:0]"
    };
    if (common_seq_type == "") void'($value$plusargs("run_%0s", common_seq_type));
    if (common_seq_type == "sec_cm_fi") begin
      for (int i = 0; i < path.size(); i++) begin
        `DV_CHECK(uvm_hdl_deposit(path[i], 0))
      end
    // Each run of sec_cm takes about 10 min.
    // Limit num_trans of sec_cm to 10.
      run_sec_cm_fi_vseq(10);
    end else run_common_vseq_wrapper(num_trans);
  endtask : body

  bit prim_tl_intg_error;

  task run_tl_intg_err_vseq_sub(string ral_name);
    if (!uvm_re_match("*prim_reg_block*", ral_name)) prim_tl_intg_error = 1;
    else prim_tl_intg_error = 0;
    super.run_tl_intg_err_vseq_sub(ral_name);
  endtask

  // Override from hw/dv/sv/cip_lib/seq_lib/cip_base_vseq__sec_cm_fi.svh
  task test_sec_cm_fi();
    sec_cm_base_if_proxy if_proxy_q[$] = sec_cm_pkg::sec_cm_if_proxy_q;

    if_proxy_q.shuffle();
    while (if_proxy_q.size) begin
      sec_cm_base_if_proxy if_proxy = if_proxy_q.pop_front();

      // If fault injection is disabled at this instance of the interface, skip it (and don't inject
      // anything)
      if (if_proxy.fi_disabled) continue;

      sec_cm_fi_ctrl_svas(if_proxy, .enable(0));
      sec_cm_inject_fault(if_proxy);

      // Randomly force the cnt to normal value (error will be cleared) to make sure design latches
      // the error
      if ($urandom_range(0, 1)) begin
        sec_cm_restore_fault(if_proxy);
      end

      if (cfg.seq_cfg.use_vendor_flash == 1 &&
          cfg.seq_cfg.vendor_flash_path != "" &&
          !uvm_re_match(cfg.seq_cfg.vendor_flash_path, if_proxy.path) == 1) begin
         wait_alert_trigger("fatal_prim_flash_alert", .wait_complete(1));
      end else begin
        // when a fault occurs at the reg_we_check, it's treated as a TL intg error
        if (if_proxy.sec_cm_type == SecCmPrimOnehot &&
            !uvm_re_match("*u_prim_reg_we_check*", if_proxy.path)) begin
          if (!uvm_re_match("*u_eflash*", if_proxy.path)) prim_tl_intg_error = 1;
          check_tl_intg_error_response();
        end else begin
          check_sec_cm_fi_resp(if_proxy);
        end
      end
      sec_cm_fi_ctrl_svas(if_proxy, .enable(1));
      // issue hard reset for fatal alert to recover
      prim_tl_intg_error = 0;
      dut_init("HARD");
    end
  endtask : test_sec_cm_fi

  virtual task check_tl_intg_error_response();
    if (prim_tl_intg_error) begin
      repeat ($urandom_range(5, 10))
        wait_alert_trigger("fatal_prim_flash_alert");
    end else begin
         super.check_tl_intg_error_response();
    end
  endtask // check_tl_intg_error_response

  virtual task check_sec_cm_fi_resp(sec_cm_base_if_proxy if_proxy);
    bit flash_dis = 1;
    `uvm_info(`gfn, $sformatf("path: %s", if_proxy.path), UVM_MEDIUM)

    if (!uvm_re_match("*.u_host_outstanding_cnt*", if_proxy.path)) begin
      collect_err_cov_status(ral.fault_status);
      csr_rd_check(.ptr(ral.fault_status.host_gnt_err), .compare_value(1));
      flash_dis = 0;
    end else begin
      super.check_sec_cm_fi_resp(if_proxy);
    end
    if (!uvm_re_match("*.u_flash_hw_if.*", if_proxy.path)) begin
      collect_err_cov_status(ral.std_fault_status);
      csr_rd_check(.ptr(ral.std_fault_status.lcmgr_err), .compare_value(1));
      // skip debug_state check because state is corrupted.
      flash_dis = 0;
    end
    if (cfg.seq_cfg.use_vendor_flash == 1 &&
        cfg.seq_cfg.vendor_flash_path != "" &&
        !uvm_re_match(cfg.seq_cfg.vendor_flash_path, if_proxy.path) == 1) begin
      flash_dis = 0;
    end
    case (if_proxy.sec_cm_type)
      SecCmPrimCount: begin
        if (!uvm_re_match("*.u_host_rsp_fifo.*", if_proxy.path) |
            !uvm_re_match("*.u_to_rd_fifo.*", if_proxy.path) |
            !uvm_re_match("*.u_rd_storage.*", if_proxy.path)) begin
          collect_err_cov_status(ral.std_fault_status);
          csr_rd_check(.ptr(ral.std_fault_status.fifo_err), .compare_value(1));
        end
        if (!uvm_re_match("*.u_flash_ctrl_rd.u_cnt*", if_proxy.path) |
            !uvm_re_match("*.u_flash_ctrl_prog.u_cnt*", if_proxy.path)) begin
          collect_err_cov_status(ral.std_fault_status);
          csr_rd_check(.ptr(ral.std_fault_status.ctrl_cnt_err), .compare_value(1));
        end
      end
      SecCmPrimSparseFsmFlop: begin
        if (!uvm_re_match("*.gen_flash_cores*", if_proxy.path)) begin
          collect_err_cov_status(ral.std_fault_status);
          csr_rd_check(.ptr(ral.std_fault_status.phy_fsm_err), .compare_value(1));
        end
        if (!uvm_re_match("*.u_ctrl_arb.*", if_proxy.path)) begin
          collect_err_cov_status(ral.std_fault_status);
          csr_rd_check(.ptr(ral.std_fault_status.arb_fsm_err), .compare_value(1));
        end
        if (!uvm_re_match("*_tl_gate.*", if_proxy.path)) begin
          collect_err_cov_status(ral.std_fault_status);
          csr_rd_check(.ptr(ral.std_fault_status.reg_intg_err), .compare_value(1));
        end
      end
      SecCmPrimOnehot: begin
        // Do nothing.
      end
      default: begin
        `uvm_fatal(`gfn, $sformatf("unexpected sec_cm_type %s", if_proxy.sec_cm_type.name))
      end
    endcase

    if (flash_dis) begin
      csr_rd_check(.ptr(ral.debug_state),
                   .compare_value(flash_ctrl_env_pkg::FlashLcDisabled));
      flash_access_after_disabled();
    end
  endtask // check_sec_cm_fi_resp

   virtual function void sec_cm_fi_ctrl_svas(sec_cm_base_if_proxy if_proxy, bit enable);
    case (if_proxy.sec_cm_type)
      SecCmPrimCount: begin
        if (enable) begin
          $asserton(0, "tb.dut.u_eflash.gen_flash_cores[0].u_core.u_rd.u_rd_storage");
          $asserton(0, "tb.dut.u_eflash.gen_flash_cores[1].u_core.u_rd.u_rd_storage");
          $asserton(0, "tb.dut.u_eflash.gen_flash_cores[0].u_host_rsp_fifo");
          $asserton(0, "tb.dut.u_eflash.gen_flash_cores[1].u_host_rsp_fifo");
          $asserton(0, "tb.dut.u_eflash.gen_flash_cores[0].u_core.u_rd.u_rsp_order_fifo");
          $asserton(0, "tb.dut.u_eflash.gen_flash_cores[1].u_core.u_rd.u_rsp_order_fifo");
          $asserton(0, "tb.dut.u_to_rd_fifo.u_rspfifo.DataKnown_A");
          $asserton(0, "tb.dut.tlul_assert_device.gen_device.dDataKnown_A");
          $asserton(0, "tb.dut.u_eflash.gen_flash_cores[0].u_core.RdTxnCheck_A");
          $asserton(0, "tb.dut.u_eflash.gen_flash_cores[1].u_core.RdTxnCheck_A");
          $asserton(0, "tb.dut.RspPayLoad_A");
        end else begin
          $assertoff(0, "tb.dut.u_eflash.gen_flash_cores[0].u_core.u_rd.u_rd_storage");
          $assertoff(0, "tb.dut.u_eflash.gen_flash_cores[1].u_core.u_rd.u_rd_storage");
          $assertoff(0, "tb.dut.u_eflash.gen_flash_cores[0].u_host_rsp_fifo");
          $assertoff(0, "tb.dut.u_eflash.gen_flash_cores[1].u_host_rsp_fifo");
          $assertoff(0, "tb.dut.u_eflash.gen_flash_cores[0].u_core.u_rd.u_rsp_order_fifo");
          $assertoff(0, "tb.dut.u_eflash.gen_flash_cores[1].u_core.u_rd.u_rsp_order_fifo");
          $assertoff(0, "tb.dut.u_to_rd_fifo.u_rspfifo.DataKnown_A");
          $assertoff(0, "tb.dut.tlul_assert_device.gen_device.dDataKnown_A");
          $assertoff(0, "tb.dut.u_eflash.gen_flash_cores[0].u_core.RdTxnCheck_A");
          $assertoff(0, "tb.dut.u_eflash.gen_flash_cores[1].u_core.RdTxnCheck_A");
          $assertoff(0, "tb.dut.u_to_rd_fifo.rvalidHighWhenRspFifoFull");
          $assertoff(0, "tb.dut.RspPayLoad_A");
        end
      end
      SecCmPrimSparseFsmFlop: begin
        if (enable) begin
          $asserton(0, "tb.dut.u_flash_hw_if.DisableChk_A");
        end else begin
          $assertoff(0, "tb.dut.u_flash_hw_if.DisableChk_A");
        end
      end
      SecCmPrimOnehot: begin
        // Do nothing.
      end
      default: begin
        `uvm_fatal(`gfn, $sformatf("unexpected sec_cm_type %s", if_proxy.sec_cm_type.name))
      end
    endcase
   endfunction

  virtual task write_and_check_update_error(dv_base_reg shadowed_csr);
    super.write_and_check_update_error(shadowed_csr);
    collect_err_cov_status(ral.err_code);
  endtask // write_and_check_update_error

  virtual task poke_and_check_storage_error(dv_base_reg shadowed_csr);
    super.poke_and_check_storage_error(shadowed_csr);
    collect_err_cov_status(ral.std_fault_status);
  endtask

endclass
