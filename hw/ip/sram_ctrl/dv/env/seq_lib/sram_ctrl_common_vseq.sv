// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class sram_ctrl_common_vseq extends sram_ctrl_base_vseq;
  `uvm_object_utils(sram_ctrl_common_vseq)

  constraint num_trans_c {
    num_trans inside {[1:2]};
  }
  `uvm_object_new

  bit first_reset;

  string path_sram_key = {`DUT_HIER_STR, ".key_q"};
  string path_sram_nonce = {`DUT_HIER_STR, ".nonce_q"};

  virtual task pre_start();
    string common_seq_type;

    `DV_CHECK_FATAL(uvm_hdl_check_path(path_sram_key))
    `DV_CHECK_FATAL(uvm_hdl_check_path(path_sram_nonce))

    void'($value$plusargs("run_%0s", common_seq_type));

    // To avoid reading out unknown data from mem, do init for mem test after 1st reset
    // Also do init for integrity test to make sure mem has correct integrity
    if ((!uvm_re_match("*mem*", common_seq_type) ||
         !uvm_re_match("*passthru_mem_tl_intg_err", common_seq_type) ||
         !uvm_re_match("*sec_cm", common_seq_type)) &&
        !first_reset) begin
      do_sram_ctrl_init = 1;
      first_reset       = 1;
    end else begin
      do_sram_ctrl_init = 0;
    end

    super.pre_start();

    // After init, init_done is set. If scb is off, update predict value here
    if (!cfg.en_scb && do_sram_ctrl_init) begin
      void'(ral.status.init_done.predict(.value(1), .kind(UVM_PREDICT_READ)));
    end

    // disable running csr_vseq, as we do sram_ctrl_init which affects several CSRs' values
    en_csr_vseq_w_passthru_mem_intg = 0;
  endtask

  virtual task body();
    run_common_vseq_wrapper(num_trans);
  endtask : body

  virtual function void inject_intg_fault_in_passthru_mem(dv_base_mem mem,
                                                          bit [bus_params_pkg::BUS_AW-1:0] addr);
    bit[bus_params_pkg::BUS_DW-1:0] rdata;
    bit[tlul_pkg::DataIntgWidth+bus_params_pkg::BUS_DW-1:0] flip_bits;

    rdata = cfg.mem_bkdr_util_h.sram_encrypt_read32_integ(addr, cfg.scb.key, cfg.scb.nonce);

    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(flip_bits,
        $countones(flip_bits) inside {[1:cip_base_pkg::MAX_TL_ECC_ERRORS]};)

    `uvm_info(`gfn, $sformatf("Backdoor change mem (addr 0x%0h) value 0x%0h by flipping bits %0h",
                              addr, rdata, flip_bits), UVM_LOW)

    cfg.mem_bkdr_util_h.sram_encrypt_write32_integ(addr, rdata, cfg.scb.key, cfg.scb.nonce,
                                                   flip_bits);
  endfunction

  // Check internal key/nonce are reset to default
  // Check sram access is blocked after a fault injection
  virtual task check_sram_access_blocked_after_fi();
    otp_ctrl_pkg::sram_key_t internal_key;
    otp_ctrl_pkg::sram_nonce_t internal_nonce;

    // all mem accesses are gated after FI
    cfg.tl_mem_access_gated = 1;
    `DV_CHECK(uvm_hdl_read(path_sram_key, internal_key))
    `DV_CHECK_EQ(internal_key, sram_ctrl_pkg::RndCnstSramKeyDefault)
    `DV_CHECK(uvm_hdl_read(path_sram_nonce, internal_nonce))
    `DV_CHECK_EQ(internal_nonce, sram_ctrl_pkg::RndCnstSramNonceDefault)

    do_rand_ops(.num_ops($urandom_range(5, 20)), .blocking(0), .exp_err_rsp(1));
    csr_utils_pkg::wait_no_outstanding_access();

  endtask : check_sram_access_blocked_after_fi

  virtual function void sec_cm_fi_ctrl_svas(sec_cm_base_if_proxy if_proxy, bit enable);
    if (!uvm_re_match("*u_tlul_adapter_sram.u_rspfifo.*", if_proxy.path)) begin
      if (enable) begin
        $asserton(0, "tb.dut.u_tlul_adapter_sram.u_rspfifo");
      end else begin
        $assertoff(0, "tb.dut.u_tlul_adapter_sram.u_rspfifo");
      end
    end
  endfunction

  // Check alert and `status.init_error` is set.
  // After injecting faults, reading any address should return 0. #10909
  virtual task check_sec_cm_fi_resp(sec_cm_base_if_proxy if_proxy);
    bit [TL_AW-1:0]  addr;
    bit [TL_DBW-1:0] mask;
    bit [TL_DW-1:0]  rdata;

    super.check_sec_cm_fi_resp(if_proxy);

    if (!uvm_re_match("*.u_tlul_adapter_sram.u_rspfifo.gen_normal_fifo.u_fifo_cnt.*",
                      if_proxy.path)) begin
      csr_rd_check(.ptr(ral.status.bus_integ_error), .compare_value(1));
    end else begin
      csr_rd_check(.ptr(ral.status.init_error), .compare_value(1));
    end

    check_sram_access_blocked_after_fi();
  endtask : check_sec_cm_fi_resp

  virtual task check_tl_intg_error_response();
    super.check_tl_intg_error_response();

    check_sram_access_blocked_after_fi();
  endtask : check_tl_intg_error_response

endclass
