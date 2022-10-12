// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence accesses the rv_dm mem interface with randomly backdoor-loaded LC state. If the LC
// state gates the rv_dm mem interface (via lc_debug_en), we are expecting to see a TLUL d_error.
class chip_rv_dm_lc_disabled_vseq extends chip_stub_cpu_base_vseq;
  `uvm_object_utils(chip_rv_dm_lc_disabled_vseq)

  `uvm_object_new
  jtag_dmi_reg_block jtag_dmi_ral;
  rand lc_state_e lc_state;

  constraint num_trans_c {
    num_trans inside {[2:20]};
  }

  // Add constraint to avoid lc_escalate_en being broadcasted and causes fatal alerts.
  constraint lc_state_c {
    lc_state != LcStScrap;
  }

  virtual function void set_handles();
    super.set_handles();
    jtag_dmi_ral = cfg.jtag_dmi_ral;
  endfunction // set_handles

  virtual task pre_start();
    cfg.chip_vif.tap_straps_if.drive(JtagTapRvDm);
    super.pre_start();
    max_outstanding_accesses = 1;
  endtask

  virtual task apply_reset(string kind = "HARD");
    fork
      if (kind inside {"HARD", "TRST"}) begin
        jtag_dmi_ral.reset("HARD");
      end
      super.apply_reset(kind);
    join
  endtask

  task rv_dm_activate();
    // "Activate" the DM to so that DM_CSRs can be written to.
    csr_wr(.ptr(jtag_dmi_ral.dmcontrol.dmactive), .value(1), .blocking(1), .predict(1));
    cfg.clk_rst_vif.wait_clks(5);
  endtask

  virtual function void backdoor_override_otp();
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(lc_state)
    cfg.mem_bkdr_util_h[Otp].otp_write_lc_partition_state(lc_state);
  endfunction

  virtual function void initialize_otp_sig_verify();
    backdoor_override_otp();
    super.initialize_otp_sig_verify();
  endfunction

  virtual function bit allow_rv_dm_access();
    if (lc_state inside {LcStTestUnlocked0, LcStTestUnlocked1, LcStTestUnlocked2,
        LcStTestUnlocked3, LcStTestUnlocked4, LcStTestUnlocked5, LcStTestUnlocked6,
        LcStTestUnlocked7, LcStRma, LcStDev}) begin
      return 1;
    end else begin
      return 0;
    end
  endfunction

  // Access check via JTAG.
  virtual task rv_dm_jtag_access_check(bit gated);
    uvm_reg_data_t wdata = $urandom();
    uvm_reg_data_t exp_data, rdata;
    // Write a random 32bit value to the sbaddress0 register.
    csr_wr(.ptr(jtag_dmi_ral.sbaddress0), .value(wdata), .blocking(1), .predict(~gated));
    cfg.clk_rst_vif.wait_clks(5);
    // Expected readback data is all-zero if the JTAG interface is gated.
    exp_data = gated ? '0 : wdata;
    `uvm_info(`gfn, $sformatf("RV_DM sbaddress0 write data %0h, expected readback data %0h",
              wdata, exp_data), UVM_HIGH)
    // Read back and compare
    csr_rd(.ptr(jtag_dmi_ral.sbaddress0), .value(rdata), .blocking(1));
    `DV_CHECK_EQ(rdata, exp_data, $sformatf(
                 "RV_DM sbaddress0 read back check failed, got 0x%x, expected 0x%x",
                 rdata, exp_data))
    cfg.clk_rst_vif.wait_clks(5);
  endtask

  // Access check via TL-UL bus.
  // TODO.

  virtual task body();

    for (int trans_i = 1; trans_i <= num_trans; trans_i++) begin
      // uvm_reg rv_dm_mem_regs[$];

      if (trans_i > 1 && $urandom_range(0, 4)) dut_init();
      `uvm_info(`gfn, $sformatf("Run iterations %0d/%0d with lc_state %0s", trans_i, num_trans,
                lc_state.name), UVM_LOW)
      rv_dm_activate();
      // if ($urandom_range(0, 1)) begin
      // Check the RV_DM gating. Since the serial interface wires
      // are gated with the lc_dft_en signal, it is sufficient to check an
      // RW'able register to verify whether the gating works or not.
      rv_dm_jtag_access_check(~allow_rv_dm_access());
      // end


      // if ($urandom_range(0, 1)) begin
      // rv_dm_activate
      //   `uvm_info(`gfn, "Check RV_DM MEM access", UVM_HIGH)
      //   jtag_dmi_ral.get_registers(rv_dm_mem_regs);
      //   rand_rw_prim_regs(rv_dm_mem_regs, ~allow_rv_dm_access());
      // end
    end
  endtask : body

endclass
