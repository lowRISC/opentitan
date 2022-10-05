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

  typedef struct packed {
    lc_ctrl_state_pkg::lc_state_e lc_state;
    lc_ctrl_state_pkg::dec_lc_state_e dec_lc_state;
  } lc_state_t;

  lc_state_t unlocked_states[8] = '{
    '{
      lc_state: LcStTestUnlocked0,
      dec_lc_state: DecLcStTestUnlocked0
     },
    '{
      lc_state: LcStTestUnlocked1,
      dec_lc_state: DecLcStTestUnlocked1
     },
    '{
      lc_state: LcStTestUnlocked2,
      dec_lc_state: DecLcStTestUnlocked2
     },
    '{
      lc_state: LcStTestUnlocked3,
      dec_lc_state: DecLcStTestUnlocked3
     },
    '{
      lc_state: LcStTestUnlocked4,
      dec_lc_state: DecLcStTestUnlocked4
     },
    '{
      lc_state: LcStTestUnlocked5,
      dec_lc_state: DecLcStTestUnlocked5
     },
    '{
      lc_state: LcStTestUnlocked6,
      dec_lc_state: DecLcStTestUnlocked6
     },
    '{
      lc_state: LcStTestUnlocked7,
      dec_lc_state: DecLcStTestUnlocked7
     }
  };

  virtual task dut_init(string reset_kind = "HARD");
    bit [TokenWidthBit-1:0] otp_exit_token_bits;
    lc_state_t temp;
    super.dut_init(reset_kind);

    // make sure we are in one of the unlocked states
    cfg.mem_bkdr_util_h[Otp].otp_write_lc_partition_state(unlocked_states[unlocked_idx].lc_state);

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

    jtag_dm_activation_seq.start(p_sequencer.jtag_sequencer_h);
    `uvm_info(`gfn, $sformatf("rv_dm_activated: %0d", cfg.m_jtag_riscv_agent_cfg.rv_dm_activated),
              UVM_LOW)
    cfg.m_jtag_riscv_agent_cfg.is_rv_dm = 1;
    jtag_otp_program32(otp_ctrl_reg_pkg::CreatorSwCfgRomExecEnOffset, 1, err);
    if (err) begin
      `uvm_error(`gfn, "Otp program failed")
    end

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
    jtag_lc_state_transition(unlocked_states[unlocked_idx].dec_lc_state,
                             DecLcStProd, {<<8{lc_exit_token}});

    // LC state transition requires a chip reset.
    `uvm_info(`gfn, "Applying reset after lc transition", UVM_LOW)
    apply_reset();

    // setup triggers to bootstrap during the second run
    cfg.chip_vif.sw_straps_if.drive({3{1'b1}});
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInBootRom)

    // bootstrap the same image
    spi_device_load_bootstrap({cfg.sw_images[SwTypeTest], ".64.vmem"});

    `DV_SPINWAIT(wait(cfg.sw_logger_vif.printed_log ==
                      "ROM and flash execution successful");,
                 "timeout waiting for C side acknowledgement",
                 cfg.sw_test_timeout_ns)

    `uvm_info(`gfn, "Received C side acknowledgement", UVM_LOW)


  endtask



endclass : chip_sw_exit_test_unlocked_bootstrap_vseq
