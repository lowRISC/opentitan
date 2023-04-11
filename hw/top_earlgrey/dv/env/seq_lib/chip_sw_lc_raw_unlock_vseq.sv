// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_lc_raw_unlock_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_lc_raw_unlock_vseq)

  `uvm_object_new

  // Mapped to plusarg to indicate that the test is run with a production ROM
  // image.
  bit rom_prod_mode = 1'b0;

  virtual task pre_start();
    void'($value$plusargs("rom_prod_mode=%0d", rom_prod_mode));
    cfg.chip_vif.tap_straps_if.drive(JtagTapLc);
    super.pre_start();
  endtask

  // reset jtag interface
  virtual task reset_jtag_tap();
    cfg.m_jtag_riscv_agent_cfg.in_reset = 1;
    #2000ns;
    cfg.m_jtag_riscv_agent_cfg.in_reset = 0;
  endtask

  virtual task clkmgr_switch_to_ext_clk();
    bit [TL_DW-1:0] status;
    bit ack = 0;
    int base_addr = top_earlgrey_pkg::TOP_EARLGREY_CLKMGR_AON_BASE_ADDR;
    bit [TL_DW-1:0] extcl_en = (
      prim_mubi_pkg::MuBi4True << ral.clkmgr_aon.extclk_ctrl.sel.get_lsb_pos() |
      prim_mubi_pkg::MuBi4False << ral.clkmgr_aon.extclk_ctrl.hi_speed_sel.get_lsb_pos()
    );

    // Switch to external system clk source in low speed mode.
    jtag_riscv_agent_pkg::jtag_write_csr(base_addr + ral.clkmgr_aon.extclk_ctrl.get_offset(),
                                         p_sequencer.jtag_sequencer_h, extcl_en);

    `uvm_info(`gfn, "Waiting for extclk transition", UVM_LOW)
    while (!ack) begin
      jtag_riscv_agent_pkg::jtag_read_csr(base_addr + ral.clkmgr_aon.extclk_status.get_offset(),
                                          p_sequencer.jtag_sequencer_h, status);

      ack = dv_base_reg_pkg::get_field_val(
          ral.clkmgr_aon.extclk_status.ack, status
      ) == prim_mubi_pkg::MuBi4True;
    end
  endtask

  virtual task body();
    bit [TokenWidthBit-1:0] otp_exit_token_bits, otp_unlock_token_bits, otp_rma_token_bits;
    bit [7:0] selected_dest_state[];

    jtag_riscv_dm_activation_seq jtag_dm_activation_seq =
        jtag_riscv_dm_activation_seq::type_id::create(
        "jtag_dm_activation_seq"
    );

    super.body();

    // Since super.body only does backdoor operation,
    // add wait for clock task before the test uses jtag polling task.
    wait_rom_check_done();
    wait_lc_ready();

    // Switch to external clock via lc_ctrl TAP, and perform RAW unlock. This
    // requires a reset to apply the transition.
    switch_to_external_clock();
    jtag_lc_state_transition(DecLcStRaw, DecLcStTestUnlocked0);
    // Complete state transition
    apply_reset();
    wait_lc_ready();

    // After reset, clock bypass back to 'off'.
    // Resume external clock before switch jtag_tap, otherwise,
    // external clock is disconnected.
    claim_transition_interface();
    jtag_riscv_agent_pkg::jtag_write_csr(
                                         ral.lc_ctrl.transition_ctrl.get_offset(),
                                         p_sequencer.jtag_sequencer_h,
                                         1);
    // Add some delay until clock bypass is turned on.
    cfg.chip_vif.aon_clk_por_rst_if.wait_clks(10);

    // Switch tap to rvdm
    cfg.chip_vif.tap_straps_if.drive(JtagTapRvDm);
    reset_jtag_tap();

    if (rom_prod_mode) begin
      // The production ROM is not instrumented to report `sw_test_status`, so
      // we wait for the PC to advance before continuing with the test. The
      // PC was taken from the ROM disassembly.
      `DV_WAIT(cfg.chip_vif.probed_cpu_pc.pc_wb >= 8194)
    end else begin
      // In RAW state the ROM should halt as RomExecEn is not set yet.
      `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInBootRomHalt)
    end

    // Use the frontend interface to configure the RomExecEn OTP value. A
    // reset is required to have otp_ctrl sample the new OTP value.
    `uvm_info(`gfn, "Configuring RomExecEn", UVM_LOW)
    jtag_dm_activation_seq.start(p_sequencer.jtag_sequencer_h);
    `uvm_info(`gfn, $sformatf("rv_dm_activated: %0d", cfg.m_jtag_riscv_agent_cfg.rv_dm_activated),
              UVM_LOW)
    cfg.m_jtag_riscv_agent_cfg.is_rv_dm = 1;
    jtag_otp_program32(otp_ctrl_reg_pkg::CreatorSwCfgRomExecEnOffset, 1);

    if (rom_prod_mode) begin
      // Use otbn mod_exp implementation for signature verification. See the
      // definition of `hardened_bool_t` in sw/device/lib/base/hardened.h.
      jtag_otp_program32(otp_ctrl_reg_pkg::CreatorSwCfgSigverifyRsaModExpIbexEnOffset, 32'h1d4);
    end

    cfg.chip_vif.tap_straps_if.drive(JtagTapRvDm);
    apply_reset();
    reset_jtag_tap();

    // Wait for `rom_ctrl` to complete the ROM check. This will give the dut
    // enough time to configure the TAP interface before any JTAG agents send
    // any commands.
    wait_rom_check_done();

    // Wait for ROM to start executing by checking PC to reach an arbitrary
    // value.
    `DV_WAIT(cfg.chip_vif.probed_cpu_pc.pc_wb >= 8194)

    `uvm_info(`gfn, "Switching to CLK_EXT via clkmgr", UVM_LOW)
    jtag_dm_activation_seq.start(p_sequencer.jtag_sequencer_h);
    `uvm_info(`gfn, $sformatf("rv_dm_activated: %0d", cfg.m_jtag_riscv_agent_cfg.rv_dm_activated),
              UVM_LOW)
    cfg.m_jtag_riscv_agent_cfg.is_rv_dm = 1;
    clkmgr_switch_to_ext_clk();

    `uvm_info(`gfn, "Check sensor_ctrl status bit set to 0", UVM_LOW)
    csr_rd_check(.ptr(ral.sensor_ctrl_aon.status.ast_init_done), .compare_value(0), .backdoor(1));

  endtask
endclass
