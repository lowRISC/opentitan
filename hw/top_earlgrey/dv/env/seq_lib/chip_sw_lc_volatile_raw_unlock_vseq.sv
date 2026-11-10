// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_lc_volatile_raw_unlock_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_lc_volatile_raw_unlock_vseq)

  `uvm_object_new

  // Mapped to plusarg to indicate that the test is run with a production ROM
  // image.
  bit rom_prod_mode = 1'b0;

  // Indicates whether we expect the volatile RAW unlock feature to be enabled in HW or not.
  bit exp_volatile_raw_unlock_en = 1'b0;

  virtual task pre_start();
    void'($value$plusargs("rom_prod_mode=%0d", rom_prod_mode));
    void'($value$plusargs("exp_volatile_raw_unlock_en=%0d", exp_volatile_raw_unlock_en));
    cfg.chip_vif.tap_straps_if.drive(JtagTapLc);
    super.pre_start();
  endtask

  // reset jtag interface
  virtual task reset_jtag_tap();
    cfg.m_jtag_riscv_agent_cfg.in_reset = 1;
    #2000ns;
    cfg.m_jtag_riscv_agent_cfg.in_reset = 0;
  endtask

  virtual task body();
    bit [TokenWidthBit-1:0] otp_exit_token_bits, otp_unlock_token_bits, otp_rma_token_bits;
    bit [7:0] selected_dest_state[];

    super.body();

    // Since super.body only does backdoor operation,
    // add wait for clock task before the test uses jtag polling task.
    `uvm_info(`gfn, "Waiting for ROM check and LC ready ...", UVM_LOW)
    wait_rom_check_done();
    wait_lc_ready(1);
    `uvm_info(`gfn, "Done.", UVM_LOW)

    if (exp_volatile_raw_unlock_en) begin
      bit [TL_DW-1:0] lc_state, device_id;
      `uvm_info(`gfn, "Expecting volatile raw unlock enabled.", UVM_LOW)
      // The test runs without the DIS_VOL_RAW_UNLOCK marker (+rram_dis_vol_raw_unlock=0), like a
      // part before forming.
      // rram_macro's zero view then hides the RRAM, so OTP reads as all zero and cannot be
      // programmed.
      // So the ROM never executes software, because RomExecEn reads as zero.
      // The test therefore only checks the volatile unlock and the zero view through the LC TAP.
      jtag_lc_state_volatile_raw_unlock(.target_strap(JtagTapLc), .expect_success(1));

      jtag_riscv_agent_pkg::jtag_read_csr(ral.lc_ctrl_regs.lc_state.get_offset(),
                                          p_sequencer.jtag_sequencer_h, lc_state);
      `DV_CHECK_EQ(lc_state, {DecLcStateNumRep{DecLcStTestUnlocked0}})

      // The zero view makes the whole OTP read as zero, including the device ID.
      foreach (ral.lc_ctrl_regs.device_id[i]) begin
        jtag_riscv_agent_pkg::jtag_read_csr(ral.lc_ctrl_regs.device_id[i].get_offset(),
                                            p_sequencer.jtag_sequencer_h, device_id);
        `DV_CHECK_EQ(device_id, 0)
      end
      `uvm_info(`gfn, "Done.", UVM_LOW)
    end else begin
      `uvm_info(`gfn, "Expecting volatile raw unlock disabled.", UVM_LOW)
      // We expect this to fail in this case.
      jtag_lc_state_volatile_raw_unlock(.target_strap(JtagTapLc), .expect_success(0));
      `uvm_info(`gfn, "Transition failed as expected.", UVM_LOW)
    end
  endtask

  task post_start();
    // SW never runs in this test.
    // Without the volatile RAW unlock feature, the transition does not succeed.
    // With it, the zero view keeps RomExecEn at zero (see body).
    override_test_status_and_finish(.passed(1));
    super.post_start();
  endtask : post_start
endclass
