// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// The prim_tlul register spaces are placeholders in open source environment.
// This sequence access prim_tlul access with randomly backdoor-loaded LC state.
// If the LC state gates the prim_tlul interface, we are expecting to see a TLUL d_error.
// In current chip-level design, only otp_ctrl's prim_tl_i/o will be gated by lc_dft_en_i.
class chip_prim_tl_access_vseq extends chip_stub_cpu_base_vseq;
  `uvm_object_utils(chip_prim_tl_access_vseq)

  `uvm_object_new

  rand lc_state_e lc_state;

  typedef enum bit [3:0] {
    NormalResponse  = 0,
    ZeroResponse    = 1,
    ErrorResponse   = 2
  } response_mode_e;

  constraint num_trans_c {
    num_trans inside {[2:10]};
  }

  // Add constraint to avoid lc_escalate_en being broadcasted and causes fatal alerts.
  constraint lc_state_c {
    lc_state != LcStScrap;
  }

  virtual function void backdoor_override_otp();
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(lc_state)
    otp_write_lc_partition_state(cfg.mem_bkdr_util_h[Otp], lc_state);
  endfunction

  virtual function void initialize_otp_sig_verify();
    backdoor_override_otp();
  endfunction

  function response_mode_e get_response_mode(bit using_prims);
    // If the CPU is disabled, the lc gate will respond with all zeros.
    if (cfg.chip_vif.get_lc_ctrl_enable_signal(LcCtrlSignalCpuEn) != lc_ctrl_pkg::On) begin
      return ZeroResponse;
    end

    // If the CPU is enabled, but we have put lc_ctrl in a state that won't allow TL access to
    // prims, we expect errors when we use prims.
    if (using_prims &&
        !(lc_state inside {LcStTestUnlocked0, LcStTestUnlocked1, LcStTestUnlocked2,
                           LcStTestUnlocked3, LcStTestUnlocked4, LcStTestUnlocked5,
                           LcStTestUnlocked6, LcStTestUnlocked7, LcStRma})) begin
      return ErrorResponse;
    end

    // Otherwise, we expect a normal response (not an error and not all zero)
    return NormalResponse;
  endfunction

  virtual task rw_csr_addr_with_gating(uvm_reg csr, response_mode_e rsp_mode);
    bit [TL_AW-1:0] addr = csr.get_address();
    bit [TL_DW-1:0] data = $urandom();
    bit [TL_DW-1:0] exp_data, fake_rdata;
    bit             expect_errors, writes_work, use_fake_rdata;

    csr_excl_item csr_excl = get_excl_item(csr);

    case (rsp_mode)
      NormalResponse: begin
        writes_work = 1;
        expect_errors = 0;
        use_fake_rdata = 0;
      end
      ZeroResponse: begin
        writes_work = 0;
        expect_errors = 0;
        use_fake_rdata = 1;
        fake_rdata = '0;
      end
      ErrorResponse: begin
        writes_work = 0;
        expect_errors = 1;
        use_fake_rdata = 1;
        fake_rdata = '1;
      end
      default: ;
    endcase

    // Apply CsrExclWrite
    if (!csr_excl.is_excl(csr, CsrExclWrite, CsrAllTests)) begin
      tl_access(.addr(addr), .write(1), .data(data), .exp_err_rsp(expect_errors));
      if (writes_work) begin
        void'(csr.predict(.value(data), .kind(UVM_PREDICT_WRITE)));
      end
    end

    tl_access(.addr(addr), .write(1), .data(data), .exp_err_rsp(expect_errors));
    if (writes_work) begin
      void'(csr.predict(.value(data), .kind(UVM_PREDICT_WRITE)));
    end

    exp_data = use_fake_rdata ? fake_rdata : `gmv(csr);
    `uvm_info(`gfn,
              $sformatf("Write addr %0h, write adata %0h, expect data %0h", addr, data, exp_data),
              UVM_HIGH);
    tl_access(.addr(addr), .write(0), .data(data), .exp_err_rsp(expect_errors), .check_exp_data(1),
              .exp_data(exp_data));
  endtask

  virtual task rand_rw_prim_regs(uvm_reg prim_regs[$], response_mode_e rsp_mode);
    `DV_CHECK_NE(prim_regs.size(), 0)
    prim_regs.shuffle();
    foreach (prim_regs[i]) rw_csr_addr_with_gating(prim_regs[i], rsp_mode);
  endtask

  virtual task body();
    for (int trans_i = 1; trans_i <= num_trans; trans_i++) begin
      uvm_reg otp_prim_regs[$];

      if (trans_i > 1 && $urandom_range(0, 4)) dut_init();
      `uvm_info(`gfn, $sformatf("Run iterations %0d/%0d with lc_state %0s", trans_i, num_trans,
                lc_state.name), UVM_LOW)

      if ($urandom_range(0, 1)) begin
        `uvm_info(`gfn, "Check OTP prim_tl access", UVM_HIGH)
        ral.otp_macro_prim.get_registers(otp_prim_regs);
        rand_rw_prim_regs(otp_prim_regs, get_response_mode(1'b1));
      end
    end
  endtask : body

endclass
