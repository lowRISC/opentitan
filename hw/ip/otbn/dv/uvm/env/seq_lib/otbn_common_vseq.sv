// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class otbn_common_vseq extends otbn_base_vseq;
  `uvm_object_utils(otbn_common_vseq)

  constraint num_trans_c {
    num_trans inside {[1:2]};
  }
  `uvm_object_new

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
    super.tl_access_w_abort(addr, write, data, completed, saw_err, mask, check_rsp, exp_err_rsp,
                            exp_data, compare_mask, check_exp_data, blocking, instr_type,
                            tl_sequencer_h, tl_intg_err_type, req_abort_pct);

    // If we see a write which causes an integrity error AND we've disabled the scoreboard (which
    // has its own predictor), we update the predicted value of the STATUS register to be LOCKED.
    if (completed && saw_err && !cfg.en_scb) begin
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
  task run_passthru_mem_tl_intg_err_vseq_sub(int num_times = 1, string ral_name);
    `uvm_info(`gfn, "Overriding run_passthru_mem_tl_intg_err_vseq_sub", UVM_HIGH)
    imem_init();
    dmem_init();
    super.run_passthru_mem_tl_intg_err_vseq_sub(num_times, ral_name);
  endtask

  virtual function void inject_intg_fault_in_passthru_mem(dv_base_mem mem,
                                                          bit [bus_params_pkg::BUS_AW-1:0] addr);
    logic [127:0] key;
    logic [63:0]  nonce;
    bit [38:0]    flip_bits;

    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(
        flip_bits,
        $countones(flip_bits) inside {[1:cip_base_pkg::MAX_TL_ECC_ERRORS]};)

    if(mem.get_name() == "imem") begin
      bit [38:0] rdata;

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
      bit [311:0] rdata;
      bit [311:0] rep_flip_bits;

      rep_flip_bits = {8{flip_bits}};

      key   = cfg.get_dmem_key();
      nonce = cfg.get_dmem_nonce();
      rdata = cfg.read_dmem_word(addr / 32, key, nonce);

      `uvm_info(`gfn,
                $sformatf("Backdoor change DMEM (addr 0x%0h) value 0x%0h by flipping bits %0h",
                          addr, rdata, rep_flip_bits),
                UVM_LOW)

      cfg.write_dmem_word(addr / 32, rdata, key, nonce, flip_bits);
    end

  endfunction

endclass
