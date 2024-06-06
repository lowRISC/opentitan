// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence accesses the rv_dm mem interface via JTAG and the TL-UL bus with randomly
// backdoor-loaded LC state. If the LC state gates the rv_dm mem interface (via lc_debug_en), we
// are expecting to see a d_error on the TL-UL bus and on JTAG we expect a read-write test to an RW
// reg to fail.
//
// Note that although this sequence runs in stub CPU mode, it still backdoor loads a valid ROM image
// so that the ROM check can complete successfully. This is needed since the TAP straps are
// currently sampled after the ROM check succeeds.
//
// TODO(#15624): the ROM dependency can be removed once the pwrmgr FSM has been simplified (due
// to the reset domain reorg). The strap sampling pulse will then be issued earlier, before the ROM
// check is performed.

class chip_rv_dm_lc_disabled_vseq extends chip_stub_cpu_base_vseq;
  `uvm_object_utils(chip_rv_dm_lc_disabled_vseq)

  `uvm_object_new
  jtag_dmi_reg_block jtag_dmi_ral;
  rand lc_state_e lc_state;

  rand bit dis_late_debug_en_otp;
  rand bit late_debug_en_reg;

  constraint num_trans_c {
    num_trans inside {[5:10]};
  }

  // Add constraint to avoid lc_escalate_en being broadcasted and causes fatal alerts.
  constraint lc_state_c {
    lc_state != LcStScrap;
  }

  virtual function void set_handles();
    super.set_handles();
    jtag_dmi_ral = cfg.jtag_dmi_ral;
  endfunction

  virtual task pre_start();
    // Select RV_DM TAP via the TAP straps.
    cfg.select_jtag = JtagTapRvDm;
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

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init(reset_kind);
    `uvm_info(`gfn, $sformatf("DUT Init with lc_state %0s", lc_state.name), UVM_LOW)

    // TODO(#15624): remove this part later.
    // We already wait for the ROM check to complete in the post_apply_reset sequence of
    // chip_stub_cpu_base_vseq. However, we need to wait a few additional cycles here since
    // the strap sampling pulse is released a few cycles after the ROM check completes.
    cfg.clk_rst_vif.wait_clks(100);

    late_debug_en_reg_update();

    `uvm_info(`gfn, "Attempt to activate RV_DM via JTAG.", UVM_MEDIUM)
    // RV_DM needs to be activated for the registers to work properly.
    // We always attempt to write this via the JTAG - even in states where the RV_DM is locked
    // so that incorrect gating behavior is not masked by the RV_DM being disabled.
    csr_wr(.ptr(jtag_dmi_ral.dmcontrol.dmactive), .value(1), .blocking(1), .predict(1));
    cfg.clk_rst_vif.wait_clks(5);
  endtask

  virtual task late_debug_en_reg_update();
    if (late_debug_en_reg) begin
      csr_wr(.ptr(ral.rv_dm_regs.late_debug_enable), .value(prim_mubi_pkg::MuBi32True));
      return;
    end
    csr_wr(.ptr(ral.rv_dm_regs.late_debug_enable), .value(prim_mubi_pkg::MuBi32False));
  endtask

  virtual function void backdoor_override_otp();
    prim_mubi_pkg::mubi8_t dis_late_dbg = prim_mubi_pkg::MuBi8False;
    cfg.mem_bkdr_util_h[Otp].otp_write_lc_partition_state(lc_state);

    if (dis_late_debug_en_otp) begin
      dis_late_dbg = prim_mubi_pkg::MuBi8True;
    end
    cfg.mem_bkdr_util_h[Otp].otp_write_hw_cfg1_partition(
      .en_sram_ifetch(prim_mubi_pkg::MuBi8False),
      .en_csrng_sw_app_read(prim_mubi_pkg::MuBi8True),
      .dis_rv_dm_late_debug(dis_late_dbg));
  endfunction

  virtual function void initialize_otp_lc_state();
    backdoor_override_otp();
  endfunction

  // Returns true if the RV_DM MEM is gated in a certain life cycle state.
  // This function also takes into account the late debug enable configuration.
  virtual function bit gate_rv_dm_mem_access();
    if (lc_state inside {LcStTestUnlocked0, LcStTestUnlocked1, LcStTestUnlocked2,
        LcStTestUnlocked3, LcStTestUnlocked4, LcStTestUnlocked5, LcStTestUnlocked6,
        LcStTestUnlocked7, LcStRma}) begin
      return 0;
    end

    if (lc_state == LcStDev) begin
      // Late debug is disabled in OTP, which defaults to rv_dm enabled in DEV lc_state.
      if (dis_late_debug_en_otp) begin
        return 0;
      end

      // Late debug is enabled via OTP and the rv_dm late debug enablement register
      // is set to true.
      if (~dis_late_debug_en_otp && late_debug_en_reg) begin
        return 0;
      end
    end

    // All other permutations should result in rv_dm disabled.
    return 1;
  endfunction

  // Returns true if the RV_DM DMI is gated in a certain life cycle state.
  virtual function bit gate_rv_dm_dmi_access();
    if (lc_state inside {LcStTestUnlocked0, LcStTestUnlocked1, LcStTestUnlocked2,
        LcStTestUnlocked3, LcStTestUnlocked4, LcStTestUnlocked5, LcStTestUnlocked6,
        LcStTestUnlocked7, LcStRma, LcStDev}) begin
      return 0;
    end else begin
      return 1;
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
  virtual task rw_csr_addr_with_gating(uvm_reg csr, bit gated);
    dv_base_reg dv_reg;
    dv_base_reg_field flds[$];
    bit [TL_AW-1:0] addr = csr.get_address();
    bit [TL_DW-1:0] data = $urandom();
    `downcast(dv_reg, csr)
    dv_reg.get_dv_base_reg_fields(flds);
    if (flds[0].get_access() inside {"RW", "WO"}) begin
      `uvm_info(`gfn, $sformatf("Write addr %0h, write adata %0h, exp error %0d",
                addr, data, gated), UVM_HIGH);
      tl_access(.addr(addr), .write(1), .data(data), .exp_err_rsp(gated));
    end
    // Most RV_DM registers cannot be predicted correctly.
    // We hence only check whether the accesses below error out or not.
    // In case of an error, the data read back must be all ones.
    if (flds[0].get_access() inside {"RW", "RO"}) begin
      `uvm_info(`gfn, $sformatf("Read addr %0h, exp error %0d",
                addr, gated), UVM_HIGH);
      tl_access(.addr(addr), .write(0), .data(data), .exp_err_rsp(gated), .exp_data('1),
                .check_exp_data(gated));
    end
  endtask

  virtual task rand_rw_regs(uvm_reg regs[$], bit gated);
    `DV_CHECK_NE(regs.size(), 0)
    regs.shuffle();
    foreach (regs[i]) rw_csr_addr_with_gating(regs[i], gated);
  endtask

  virtual task body();
    uvm_reg rv_dm_mem_regs[$];

    for (int trans_i = 1; trans_i <= num_trans; trans_i++) begin
      // Re-randomize the life cycle state in most iterations.
      if (trans_i > 1 && $urandom_range(0, 4)) begin
        `DV_CHECK_MEMBER_RANDOMIZE_FATAL(dis_late_debug_en_otp);
        `DV_CHECK_MEMBER_RANDOMIZE_FATAL(late_debug_en_reg);
        `DV_CHECK_MEMBER_RANDOMIZE_FATAL(lc_state)
        dut_init();
      end
      `uvm_info(`gfn, $sformatf("Run iterations %0d/%0d with lc_state %0s", trans_i, num_trans,
                lc_state.name), UVM_LOW);

      if (lc_state == LcStDev) begin
        `uvm_info(`gfn, $sformatf(
                  "Disable late debug enable in otp: %0d, enable debug in rv_dm: %0d",
                  dis_late_debug_en_otp, late_debug_en_reg), UVM_LOW);
      end

      // Check the RV_DM gating via JTAG. Since the serial JTAG interface wires are gated with the
      // lc_dft_en signal, it is sufficient to check an RW'able register to verify whether the
      // gating works or not.
      if ($urandom_range(0, 1)) begin
        // TODO: Verify that when gate_rv_dm_mem_access() is true and
        // gate_rv_dm_dmi_access() is false, SBA transactions are blocked by
        // rv_dm.
        rv_dm_jtag_access_check(gate_rv_dm_dmi_access());
      end

      // Check RV_DM gating via the TL-UL bus.
      if ($urandom_range(0, 1)) begin
        ral.rv_dm_mem.get_registers(rv_dm_mem_regs);
        rand_rw_regs(rv_dm_mem_regs, gate_rv_dm_mem_access());
      end
    end

    // Force LcStDev with late debug disabled followed by enabled. This is to
    // ensure rv_dm will support the late debug enablement during the same
    // power cycle.
    lc_state = LcStDev;
    dis_late_debug_en_otp = 0;
    late_debug_en_reg = 0;
    dut_init();
    ral.rv_dm_mem.get_registers(rv_dm_mem_regs);

    // This sequence verifies to rv_dm disabled.
    rv_dm_jtag_access_check(gate_rv_dm_dmi_access());
    rand_rw_regs(rv_dm_mem_regs, gate_rv_dm_mem_access());

    late_debug_en_reg = 1;
    late_debug_en_reg_update();

    // This sequence verifies rv_dm enabled.
    rv_dm_jtag_access_check(gate_rv_dm_dmi_access());
    rand_rw_regs(rv_dm_mem_regs, gate_rv_dm_mem_access());
  endtask : body

endclass
