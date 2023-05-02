// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_lc_volatile_raw_unlock_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_lc_volatile_raw_unlock_vseq)

  `uvm_object_new

  virtual task pre_start();
    cfg.chip_vif.tap_straps_if.drive(JtagTapLc);
    super.pre_start();
  endtask

  // reset jtag interface
  virtual task reset_jtag_tap();
    cfg.m_jtag_riscv_agent_cfg.in_reset = 1;
    #1000ns;
    cfg.m_jtag_riscv_agent_cfg.in_reset = 0;
  endtask

  virtual task body();
    bit [TokenWidthBit-1:0] otp_exit_token_bits, otp_unlock_token_bits, otp_rma_token_bits;
    bit [7:0] selected_dest_state[];

    jtag_riscv_dm_activation_seq jtag_dm_activation_seq =
        jtag_riscv_dm_activation_seq::type_id::create("jtag_dm_activation_seq");

    super.body();

    wait_lc_ready(1);

    // VOLATILE_RAW_UNLOCK does not require a reset after completion.
    // Applying a reset will move the device back to RAW state in this case.
    jtag_lc_state_volatile_raw_unlock(JtagTapRvDm);
    reset_jtag_tap();

    // In RAW state the ROM should halt as RomExecEn is not set yet.
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInBootRomHalt)

    // Use the frontend interface to configure the RomExecEn OTP value. A
    // reset is required to have otp_ctrl sample the new OTP value.
    `uvm_info(`gfn, "Configuring RomExecEng", UVM_LOW)
    jtag_dm_activation_seq.start(p_sequencer.jtag_sequencer_h);
    `uvm_info(`gfn, $sformatf("rv_dm_activated: %0d", cfg.m_jtag_riscv_agent_cfg.rv_dm_activated),
            UVM_LOW)
    cfg.m_jtag_riscv_agent_cfg.is_rv_dm = 1;
    jtag_otp_program32(otp_ctrl_reg_pkg::CreatorSwCfgRomExecEnOffset, 1);

    cfg.chip_vif.tap_straps_if.drive(JtagTapLc);
    cfg.m_jtag_riscv_agent_cfg.is_rv_dm = 0;
    apply_reset();

    // Second VOLATILE_RAW_UNLOCK does not change the TAP interface to rv_dm
    // so that we can check the completion status through that interface.
    // After this, the rest of the test should proceed.
    jtag_lc_state_volatile_raw_unlock(JtagTapLc);

  endtask
endclass
