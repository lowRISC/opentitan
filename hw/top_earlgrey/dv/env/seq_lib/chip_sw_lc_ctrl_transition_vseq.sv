// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_lc_ctrl_transition_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_lc_ctrl_transition_vseq)

  `uvm_object_new

  virtual task dut_init(string reset_kind = "HARD");
    bit [otp_ctrl_reg_pkg::TestUnlockTokenSize-1:0] rand_unlock_token;
    `DV_CHECK_STD_RANDOMIZE_FATAL(rand_unlock_token)

    super.dut_init(reset_kind);

    // Override the LC partition to TestUnlocked2.
    cfg.mem_bkdr_util_h[Otp].otp_write_lc_partition(lc_ctrl_state_pkg::LcStTestUnlocked2);

    // Override the test exit token to match SW test's input token.
    // TODO: randomize the exit_token.
    cfg.mem_bkdr_util_h[Otp].otp_write_secret0_partition(
        .unlock_token(rand_unlock_token),
        .exit_token('h547070d7503264af5b9a971b894ef3be));
  endtask

  virtual task body();
    super.body();

     // Select LC jtag.
    cfg.tap_straps_vif.drive(SelectLCJtagTap);

    // Wait for SW to finish set up LC_CTRL.
    cfg.clk_rst_vif.wait_clks(21000);

    while(1) begin
      bit [TL_DW-1:0]  status_val;
      lc_ctrl_status_e dummy;
      cfg.clk_rst_vif.wait_clks($urandom_range(0, 10));
      jtag_riscv_agent_pkg::jtag_read_csr(ral.lc_ctrl.status.get_offset(),
                                          p_sequencer.jtag_sequencer_h,
                                          status_val);

      // Ensure that none of the other status bits are set.
      `DV_CHECK_EQ(status_val >> dummy.num(), 0,
                   $sformatf("Unexpected status error %0h", status_val))
      if (status_val[LcTransitionSuccessful]) break;
    end

    // Issue hard reset.
    apply_reset();
  endtask

endclass
