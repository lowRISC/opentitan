// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_flash_rma_unlocked_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_flash_rma_unlocked_vseq)

  `uvm_object_new

  // LC sends two 64-bit msg as input token.
  localparam uint TokenWidthBit = kmac_pkg::MsgWidth * 2;
  localparam uint TokenWidthByte = TokenWidthBit / 8;
  localparam uint KeyWidthBit = otp_ctrl_reg_pkg::CreatorRootKeyShare0Size * 8;
  localparam uint KeyWidthByte = KeyWidthBit / 8;

  localparam string LC_CTRL_TRANS_SUCCESS_PATH =
    "tb.dut.top_earlgrey.u_lc_ctrl.u_lc_ctrl_fsm.trans_success_o";

  // TODO(lowRISC/opentitan:#11795): replace with SW symbol backdoor write
  // when this is fixed for ROM.
  // Currently using retention SRAM to pass test_phase to program.
  localparam string SRAM_CTRL_RET_HDL_PATH = "tb.dut.top_earlgrey.u_sram_ctrl_ret_aon";
  localparam string SRAM_CTRL_RET_NONCE_PATH = {SRAM_CTRL_RET_HDL_PATH, ".nonce_q"};
  localparam string SRAM_CTRL_RET_KEY_PATH = {SRAM_CTRL_RET_HDL_PATH, ".key_q"};

  bit [sram_scrambler_pkg::SRAM_BLOCK_WIDTH-1:0] sram_ret_nonce;
  bit [sram_scrambler_pkg::SRAM_KEY_WIDTH-1:0] sram_ret_key;

  // TODO(lowRISC/opentitan:#11795): replace with SW symbol backdoor write
  // when this is fixed for ROM.
  // Currently a fixed unlock token which will match in software.
  bit [7:0] rma_unlock_token[TokenWidthByte] = '{
      8'h00,
      8'h01,
      8'h02,
      8'h03,
      8'h04,
      8'h05,
      8'h06,
      8'h07,
      8'h08,
      8'h09,
      8'h0a,
      8'h0b,
      8'h0c,
      8'h0d,
      8'h0e,
      8'h0f
  };

  rand bit [7:0] creator_root_key0[KeyWidthByte];
  rand bit [7:0] creator_root_key1[KeyWidthByte];

  // This function takes the token value from LC_CTRL token CSRs, then runs through cshake128 to
  // get a 768-bit XORed token output.
  // The first 128 bits of the decoded token should match the OTP's secret2 paritition's
  // descrambled tokens value.
  virtual function bit [TokenWidthBit-1:0] get_otp_token(bit [7:0] token_in[TokenWidthByte]);
    bit [7:0] dpi_digest[kmac_pkg::AppDigestW/8];
    bit [kmac_pkg::AppDigestW-1:0] digest_bits;

    digestpp_dpi_pkg::c_dpi_cshake128(token_in, "", "LC_CTRL", TokenWidthByte,
                                      kmac_pkg::AppDigestW / 8, dpi_digest);

    digest_bits = {<<byte{dpi_digest}};
    return (digest_bits[TokenWidthBit-1:0]);
  endfunction

  virtual function bit [KeyWidthBit-1:0] get_otp_key(bit [7:0] key_in[KeyWidthByte]);
    bit [kmac_pkg::AppDigestW-1:0] digest_bits;
    bit [7:0] dpi_digest[kmac_pkg::AppDigestW/8];

    digestpp_dpi_pkg::c_dpi_cshake128(key_in, "", "LC_CTRL", KeyWidthByte, kmac_pkg::AppDigestW / 8,
                                      dpi_digest);

    digest_bits = {<<byte{dpi_digest}};
    return (digest_bits[KeyWidthBit-1:0]);
  endfunction

  // When the RMA transition has been completed the CPU will be disabled
  // and therefore it cannot be detected in SW. Detect this transition here
  // to allow the CPU to be reset.
  virtual task wait_for_transition();
    int retval;
    int transition_success = 0;
    retval = uvm_hdl_check_path(LC_CTRL_TRANS_SUCCESS_PATH);
    `DV_CHECK_EQ_FATAL(retval, 1, $sformatf(
                       "Hierarchical path %0s appears to be invalid.", LC_CTRL_TRANS_SUCCESS_PATH))
    while (transition_success == 0) begin
      retval = uvm_hdl_read(LC_CTRL_TRANS_SUCCESS_PATH, transition_success);
      `DV_CHECK_EQ(retval, 1, $sformatf("uvm_hdl_read failed for %0s", LC_CTRL_TRANS_SUCCESS_PATH))
      cfg.clk_rst_vif.wait_clks(1);
    end
  endtask

  // TODO(lowRISC/opentitan:#11795): replace with SW symbol backdoor write
  // when this is fixed for ROM.
  // Currently using retention SRAM to pass test_phase to program.
  // Initial write to retention SRAM with a value of zero for
  // test phase.
  virtual task ret_backdoor_write();
    int retval;
    retval = uvm_hdl_read(SRAM_CTRL_RET_NONCE_PATH, sram_ret_nonce);
    retval = uvm_hdl_read(SRAM_CTRL_RET_KEY_PATH, sram_ret_key);
    ret_sram_bkdr_write32(0, 0, sram_ret_key, sram_ret_nonce);
  endtask

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init(reset_kind);
    // Override the LC partition to Dev state.
    cfg.mem_bkdr_util_h[Otp].otp_write_lc_partition_state(LcStDev);
    // TODO(lowRISC/opentitan:#11795): replace with SW symbol backdoor write
    // when this is fixed for ROM.
    // The following overwrite does not yet work.
    sw_symbol_backdoor_overwrite("kLcRmaUnlockToken", rma_unlock_token, Rom, SwTypeRom);
  endtask

  virtual task body();
    // First Boot.
    super.body();

    // TODO(lowRISC/opentitan:#11795): replace with SW symbol backdoor write
    // when this is fixed for ROM.
    // Disable SRAM data integrity checks and do SRAM write.
    cfg.disable_d_user_data_intg_check_for_passthru_mem = 1;
    cfg.en_scb_mem_chk = 0;
    ret_backdoor_write();

    wait(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInTest);
    wait(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInWfi);
    apply_reset();

    // Second Boot.
    // Override the rma unlock token to match SW test's input token.
    cfg.mem_bkdr_util_h[Otp].otp_write_secret2_partition(
        .rma_unlock_token(get_otp_token(rma_unlock_token)),
        .creator_root_key0(get_otp_key(creator_root_key0)),
        .creator_root_key1(get_otp_key(creator_root_key1)));

    wait(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInTest);
    wait(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInWfi);

    wait_for_transition();
    cfg.clk_rst_vif.wait_clks(1000);
    apply_reset();

    // Third Boot.
    wait(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInTest);

  endtask

endclass
