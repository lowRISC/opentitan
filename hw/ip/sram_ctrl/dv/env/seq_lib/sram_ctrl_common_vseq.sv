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

  virtual task pre_start();
    string common_seq_type;
    void'($value$plusargs("run_%0s", common_seq_type));

    // To avoid reading out unknown data from mem, do init for mem test after 1st reset
    // Also do init for integrity test to make sure mem has correct integrity
    if ((!uvm_re_match("*mem*", common_seq_type) ||
         !uvm_re_match("*passthru_mem_tl_intg_err", common_seq_type)) &&
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

  // Check alert and `status.init_error` is set.
  // After injecting faults, reading any address should return 0. #10909
  virtual task check_sec_cm_fi_resp(sec_cm_base_if_proxy if_proxy);
    bit [TL_AW-1:0]  addr;
    bit [TL_DBW-1:0] mask;
    bit [TL_DW-1:0]  rdata;

    super.check_sec_cm_fi_resp(if_proxy);

    csr_rd_check(.ptr(ral.status.init_error), .compare_value(1));

    // intg won't be correct after injecting faults
    cfg.disable_d_user_data_intg_check_for_passthru_mem = 1;
    repeat ($urandom_range(1, 10)) begin
      `DV_CHECK_STD_RANDOMIZE_FATAL(addr)
      mask = get_rand_mask(.write(0));
      do_single_read(.addr(addr), .mask(mask), .rdata(rdata), .check_rdata(1),
                     .exp_rdata(0));
      `uvm_info(`gfn, $sformatf("addr: 0x%0h mask: 'b%0b, rdata: 0x%0h",
                                addr, mask, rdata), UVM_HIGH)
    end
    cfg.disable_d_user_data_intg_check_for_passthru_mem = 0;
  endtask : check_sec_cm_fi_resp
endclass
