// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class otbn_common_vseq extends otbn_base_vseq;
  `uvm_object_utils(otbn_common_vseq)
  bit sb_setting;
  constraint num_trans_c {
    num_trans inside {[1:2]};
  }
  `uvm_object_new

  function void disable_fi_for_prim_count(string path);
    sec_cm_pkg::find_sec_cm_if_proxy(.path({path, "*u_rptr"}), .is_regex(1)).disable_fi();
    sec_cm_pkg::find_sec_cm_if_proxy(.path({path, "*u_wptr"}), .is_regex(1)).disable_fi();
  endfunction

  task dut_init(string reset_kind = "HARD");
    // Disable fault injection on the prim_count module associated with the DMEM/IMEM request fifos.
    //
    // This is because injecting a fault causes a spurious TL transaction whose response eventually
    // causes a fatal alert (good). Unfortunately, the FIFO might actually have been empty, so lots
    // of signals in the design become X. This includes OTBN's status signal and we never get to the
    // "LOCKED" status because we're stuck at X. The code here disables fault injection at that
    // location.
    disable_fi_for_prim_count("*u_tlul_adapter_sram_dmem*u_reqfifo*u_fifo_cnt");
    disable_fi_for_prim_count("*u_tlul_adapter_sram_dmem*u_sramreqfifo*u_fifo_cnt");
    disable_fi_for_prim_count("*u_tlul_adapter_sram_imem*u_reqfifo*u_fifo_cnt");
    disable_fi_for_prim_count("*u_tlul_adapter_sram_imem*u_sramreqfifo*u_fifo_cnt");

    super.dut_init(reset_kind);
  endtask

  virtual task body();
    enable_base_alert_checks = 1'b1;

    run_common_vseq_wrapper(num_trans);
  endtask : body

  // Overriding a method from cip_base_vseq. This is only necessary when running the common
  // sequences (where we might turn off the scoreboard and its predictor, but still check register
  // values are as expected).
  task tl_access_w_abort(input bit [BUS_AW-1:0]    addr,
                         input bit                 write,
                         inout bit [BUS_DW-1:0]    data,
                         output bit                completed,
                         output bit                saw_err,
                         input uint             tl_access_timeout_ns = default_spinwait_timeout_ns,
                         input bit [BUS_DBW-1:0]   mask = '1,
                         input bit                 check_rsp = 1'b1,
                         input bit                 exp_err_rsp = 1'b0,
                         input bit [BUS_DW-1:0]    exp_data = 0,
                         input bit [BUS_DW-1:0]    compare_mask = '1,
                         input bit                 check_exp_data = 1'b0,
                         input bit                 blocking = csr_utils_pkg::default_csr_blocking,
                         input mubi4_t             instr_type = MuBi4False,
                         tl_sequencer              tl_sequencer_h = p_sequencer.tl_sequencer_h,
                         input tl_intg_err_e       tl_intg_err_type = TlIntgErrNone,
                         input int                 req_abort_pct = 0);
    super.tl_access_w_abort(addr, write, data, completed, saw_err, tl_access_timeout_ns, mask,
                            check_rsp, exp_err_rsp, exp_data, compare_mask, check_exp_data,
                            blocking, instr_type, tl_sequencer_h, tl_intg_err_type, req_abort_pct);

    // If we see a write which causes an integrity error AND we've disabled the scoreboard (which
    // has its own predictor), we update the predicted value of the STATUS register to be LOCKED.
    if (completed && saw_err && !cfg.en_scb && tl_intg_err_type != TlIntgErrNone) begin
      `DV_WAIT(!(cfg.model_agent_cfg.vif.status inside {otbn_pkg::StatusBusyExecute,
                                                     otbn_pkg::StatusBusySecWipeInt}));
      `DV_CHECK_FATAL(ral.status.status.predict(otbn_pkg::StatusLocked, .kind(UVM_PREDICT_READ)),
                      "Failed to update STATUS register")
    end
  endtask

  // Overridden from cip_base_vseq. Disable the MatchingStatus_A assertion from the testbench for
  // this sequence. This assertion checks that the model's STATUS register matches the DUT. Since we
  // don't actually start the processor or model (or, indeed, tell the model about the error), this
  // assertion will be false.
  task run_tl_intg_err_vseq(int num_times = 1);
    `DV_ASSERT_CTRL_REQ("otbn_status_assert_en", 1'b0)
    super.run_tl_intg_err_vseq(num_times);
    `DV_ASSERT_CTRL_REQ("otbn_status_assert_en", 1'b1)
  endtask

  // Overriden from cip_base_vseq. Initialise Imem and Dmem and then call the super function.
  task run_passthru_mem_tl_intg_err_vseq_sub(string ral_name);
    `uvm_info(`gfn, "Overriding run_passthru_mem_tl_intg_err_vseq_sub", UVM_HIGH)
    imem_init();
    dmem_init();
    super.run_passthru_mem_tl_intg_err_vseq_sub(ral_name);
  endtask

  virtual function void inject_intg_fault_in_passthru_mem(dv_base_mem mem,
                                                          bit [bus_params_pkg::BUS_AW-1:0] addr);
    logic [otp_ctrl_pkg::OtbnKeyWidth-1:0]   key;
    logic [otp_ctrl_pkg::OtbnNonceWidth-1:0] nonce;
    bit [BaseIntgWidth-1:0]                  flip_bits;

    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(
        flip_bits,
        $countones(flip_bits) inside {[1:cip_base_pkg::MAX_TL_ECC_ERRORS]};)

    if(mem.get_name() == "imem") begin
      bit [BaseIntgWidth-1:0] rdata;

      key   = cfg.get_imem_key();
      nonce = cfg.get_imem_nonce();
      rdata = cfg.read_imem_word(addr / 4, key, nonce);
      `uvm_info(`gfn,
                $sformatf("Backdoor change IMEM (addr 0x%0h) value 0x%0h by flipping bits %0h",
                          addr, rdata, flip_bits),
                UVM_LOW)
      cfg.write_imem_word(addr / 4, rdata, key, nonce, flip_bits);
    end
    else begin
      bit [ExtWLEN-1:0] rdata;
      bit [ExtWLEN-1:0] rep_flip_bits;

      rep_flip_bits = {BaseWordsPerWLEN{flip_bits}};

      key   = cfg.get_dmem_key();
      nonce = cfg.get_dmem_nonce();
      rdata = cfg.read_dmem_word(addr / (4 * BaseWordsPerWLEN), key, nonce);

      `uvm_info(`gfn,
                $sformatf("Backdoor change DMEM (addr 0x%0h) value 0x%0h by flipping bits %0h",
                          addr, rdata, rep_flip_bits),
                UVM_LOW)

      cfg.write_dmem_word(addr / (4 * BaseWordsPerWLEN), rdata, key, nonce, rep_flip_bits);
    end

  endfunction

  virtual task check_sec_cm_fi_resp(sec_cm_base_if_proxy if_proxy);
    uvm_reg_field fatal_cause;
    super.check_sec_cm_fi_resp(if_proxy);

    if (if_proxy.sec_cm_type == SecCmPrimCount &&
        !uvm_re_match("*.u_tlul_adapter_sram_*", if_proxy.path)) begin
      // Faults injected into the counters of an OTBN TLUL adapter manifest as bus integrity
      // violation.
      fatal_cause = ral.fatal_alert_cause.bus_intg_violation;
    end else begin
      fatal_cause = ral.fatal_alert_cause.bad_internal_state;
    end

    csr_utils_pkg::csr_rd_check(.ptr(fatal_cause), .compare_value(1));
    `DV_WAIT(!(cfg.model_agent_cfg.vif.status inside {otbn_pkg::StatusBusyExecute,
                                                      otbn_pkg::StatusBusySecWipeInt}));
    csr_utils_pkg::csr_rd_check(.ptr(ral.status), .compare_value('hFF));
  endtask : check_sec_cm_fi_resp

  virtual function void sec_cm_fi_ctrl_svas(sec_cm_base_if_proxy if_proxy, bit enable);
    if (enable) begin
      $asserton(0, "tb.dut.u_otbn_core.u_otbn_controller.ControllerStateValid");
      $asserton(0, "tb.MatchingStatus_A");
      $asserton(0, "tb.MatchingReqURND_A");
      $asserton(0, "tb.dut.u_otbn_core.u_otbn_start_stop_control.StartStopStateValid_A");
    end else begin
      $assertoff(0, "tb.dut.u_otbn_core.u_otbn_controller.ControllerStateValid");
      $assertoff(0, "tb.MatchingStatus_A");
      $assertoff(0, "tb.MatchingReqURND_A");
      $assertoff(0, "tb.dut.u_otbn_core.u_otbn_start_stop_control.StartStopStateValid_A");
    end
    if (if_proxy.sec_cm_type == SecCmPrimCount) begin
      cfg.model_agent_cfg.vif.otbn_disable_stack_check();
      $assertoff(0, "tb.dut.u_otbn_core.u_otbn_controller.u_otbn_loop_controller.loop_info_stack\
               .next_stack_top_idx_correct");
      $assertoff(0, "tb.dut.u_otbn_core.u_otbn_rf_base.u_call_stack.next_stack_top_idx_correct");
      if (if_proxy.path == {"tb.dut.u_tlul_adapter_sram_dmem.u_rspfifo.gen_normal_fifo.u_fifo_cnt.",
                            "gen_secure_ptrs.u_wptr"} ||
          if_proxy.path == {"tb.dut.u_tlul_adapter_sram_dmem.u_rspfifo.gen_normal_fifo.u_fifo_cnt.",
                            "gen_secure_ptrs.u_rptr"}) begin
        if (enable) begin
          $asserton(0, "tb.dut.u_tlul_adapter_sram_dmem.u_rspfifo.DataKnown_A");
        end else begin
          $assertoff(0, "tb.dut.u_tlul_adapter_sram_dmem.u_rspfifo.DataKnown_A");
        end
      end
      if (if_proxy.path == {"tb.dut.u_tlul_adapter_sram_imem.u_rspfifo.gen_normal_fifo.u_fifo_cnt.",
                            "gen_secure_ptrs.u_wptr"} ||
          if_proxy.path == {"tb.dut.u_tlul_adapter_sram_imem.u_rspfifo.gen_normal_fifo.u_fifo_cnt.",
                            "gen_secure_ptrs.u_rptr"}) begin
        if (enable) begin
          $asserton(0, "tb.dut.u_tlul_adapter_sram_imem.u_rspfifo.DataKnown_A");
        end else begin
          $assertoff(0, "tb.dut.u_tlul_adapter_sram_imem.u_rspfifo.DataKnown_A");
        end
      end
    end

  endfunction: sec_cm_fi_ctrl_svas

  virtual task sec_cm_inject_fault(sec_cm_base_if_proxy if_proxy);
    fork
      begin
        if_proxy.inject_fault();
      end
      begin
        bit [31:0] err_val = 32'd1 << 20;
        `uvm_info(`gfn, "injecting fsm error into ISS", UVM_HIGH)
        if (!uvm_re_match("*u_otbn_start_stop_control*", if_proxy.path)) begin
          cfg.model_agent_cfg.vif.lock_immediately(err_val);
        end else begin
          cfg.model_agent_cfg.vif.send_err_escalation(err_val);
        end
      end
    join
  endtask : sec_cm_inject_fault

  virtual task pre_run_sec_cm_fi_vseq();
    sb_setting = cfg.en_scb;
    cfg.en_scb = 1;
  endtask : pre_run_sec_cm_fi_vseq

  virtual task post_run_sec_cm_fi_vseq();
    cfg.en_scb = sb_setting;
  endtask : post_run_sec_cm_fi_vseq


endclass
