// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_exit_test_unlocked_bootstrap_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_exit_test_unlocked_bootstrap_vseq)

  `uvm_object_new

  rand int unlocked_idx;
  constraint idx_c {
    unlocked_idx inside {[0:7]};
  }

  rand bit [7:0] lc_exit_token[TokenWidthByte];

  virtual task dut_init(string reset_kind = "HARD");
    bit [TokenWidthBit-1:0] otp_exit_token_bits;
    super.dut_init(reset_kind);

    // make sure we are in one of the unlocked states
    cfg.mem_bkdr_util_h[Otp].otp_write_lc_partition_state(UnlockedStates[unlocked_idx].lc_state);

    // backdoorload the otp tokens and associated digest
    otp_exit_token_bits = dec_otp_token_from_lc_csrs(lc_exit_token);
    cfg.mem_bkdr_util_h[Otp].otp_write_secret0_partition(
      '0, otp_exit_token_bits);

    //ensure rom_exec_en is 0, so that flash is never reached
    cfg.mem_bkdr_util_h[Otp].write32(otp_ctrl_reg_pkg::CreatorSwCfgRomExecEnOffset, 0);

  endtask

  // reset jtag interface
  virtual task reset_jtag_tap();
    cfg.m_jtag_riscv_agent_cfg.in_reset = 1;
    #1000ns;
    cfg.m_jtag_riscv_agent_cfg.in_reset = 0;
  endtask

  virtual task body();
    bit err = 0;
    jtag_riscv_dm_activation_seq jtag_dm_activation_seq =
        jtag_riscv_dm_activation_seq::type_id::create("jtag_dm_activation_seq");

    super.body();

    // The test sequence needs to ensure rom has halted first.
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInBootRomHalt)

    // Now program ROM_EXEC_EN for next power cycle.
    cfg.chip_vif.tap_straps_if.drive(JtagTapRvDm);

    // Add delay before drive jtag after strap switch.
    cfg.clk_rst_vif.wait_clks(5);
    jtag_dm_activation_seq.start(p_sequencer.jtag_sequencer_h);
    `uvm_info(`gfn, $sformatf("rv_dm_activated: %0d", cfg.m_jtag_riscv_agent_cfg.rv_dm_activated),
              UVM_LOW)
    cfg.m_jtag_riscv_agent_cfg.is_rv_dm = 1;
    jtag_otp_program32(otp_ctrl_reg_pkg::CreatorSwCfgRomExecEnOffset, 1);


    // Reset tap interface for switch.
    reset_jtag_tap();

    // Prepare LC JTAG interface
    cfg.chip_vif.tap_straps_if.drive(JtagTapLc);
    cfg.clk_rst_vif.wait_clks(10);
    cfg.m_jtag_riscv_agent_cfg.is_rv_dm = 0;

    for (int i = 0; i < TokenWidthByte; i++) begin
      `uvm_info(`gfn, $sformatf("LC exit token 0x%x", lc_exit_token[i]), UVM_MEDIUM)
    end

    // TODO: Should consider applying a random large delay here to simulate different
    // host side timing.
    // Transition device into production state.
    jtag_lc_state_transition(UnlockedStates[unlocked_idx].dec_lc_state,
                             DecLcStProd, {<<8{lc_exit_token}});

    // LC state transition requires a chip reset.
    `uvm_info(`gfn, "Applying reset after lc transition", UVM_LOW)
    apply_reset();

    // setup triggers to bootstrap during the second run
    cfg.use_spi_load_bootstrap = 1'b1;
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInBootRom)

    // bootstrap the same image
    spi_device_load_bootstrap({cfg.sw_images[SwTypeTestSlotA], ".64.vmem"});

    // Disable bootstrap for subsequent boots.
    cfg.use_spi_load_bootstrap = 1'b0;
  endtask : body

endclass : chip_sw_exit_test_unlocked_bootstrap_vseq
