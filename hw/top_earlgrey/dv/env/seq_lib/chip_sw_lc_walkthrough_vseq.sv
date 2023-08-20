// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_lc_walkthrough_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_lc_walkthrough_vseq)

  `uvm_object_new

  // LC sends two 64-bit msg as input token.
  localparam uint TokenWidthBit  = kmac_pkg::MsgWidth * 2;
  localparam uint TokenWidthByte = TokenWidthBit / 8;

  rand bit [7:0] lc_exit_token[TokenWidthByte];
  rand bit [7:0] lc_unlock_token[TokenWidthByte];
  rand bit [7:0] lc_rma_token[TokenWidthByte];
  bit [7:0] otp_exit_token[TokenWidthByte];
  bit [7:0] otp_unlock_token[TokenWidthByte];
  bit [7:0] otp_rma_token[TokenWidthByte];

  lc_ctrl_state_pkg::dec_lc_state_e dest_dec_state = lc_ctrl_state_pkg::DecLcStProdEnd;

  virtual task pre_start();
    `DV_GET_ENUM_PLUSARG(lc_ctrl_state_pkg::dec_lc_state_e, dest_dec_state, dest_dec_state)
    `uvm_info(`gfn, $sformatf("Destination state is %0s", dest_dec_state.name), UVM_MEDIUM)
    cfg.chip_vif.tap_straps_if.drive(JtagTapLc);
    super.pre_start();
  endtask

  virtual task apply_reset(string kind = "HARD");
    super.apply_reset();
    // Wait for `rom_ctrl` to complete the ROM check. This will give the dut
    // enough time to configure the TAP interface before any JTAG agents send
    // any commands.
    wait_rom_check_done();
    set_otp_creator_sw_cfg_rom_exec_en(1);
  endtask

  virtual task body();
    bit [TokenWidthBit-1:0] otp_exit_token_bits, otp_unlock_token_bits, otp_rma_token_bits;
    bit [7:0] selected_dest_state[];
    super.body();

    otp_exit_token_bits = dec_otp_token_from_lc_csrs(lc_exit_token);
    otp_unlock_token_bits = dec_otp_token_from_lc_csrs(lc_unlock_token);
    otp_rma_token_bits = dec_otp_token_from_lc_csrs(lc_rma_token);

    otp_unlock_token = {<< 8{otp_unlock_token_bits}};
    otp_exit_token = {<< 8{otp_exit_token_bits}};
    otp_rma_token = {<< 8{otp_rma_token_bits}};

    `uvm_info(`gfn, $sformatf("OTP unlock token %0h and OTP exit token %0h",
              otp_unlock_token_bits, otp_exit_token_bits), UVM_LOW)

    // Override the C test tokens with random data.
    sw_symbol_backdoor_overwrite("kLcExitToken", lc_exit_token);
    sw_symbol_backdoor_overwrite("kOtpExitToken", otp_exit_token);
    sw_symbol_backdoor_overwrite("kOtpUnlockToken", otp_unlock_token);
    sw_symbol_backdoor_overwrite("kLcRmaToken", lc_rma_token);
    sw_symbol_backdoor_overwrite("kOtpRmaToken", otp_rma_token);

    // Override the C test destination state with the plusarg value.
    selected_dest_state = {dest_dec_state};
    sw_symbol_backdoor_overwrite("kDestState", selected_dest_state);

    switch_to_external_clock();
    jtag_lc_state_transition(DecLcStRaw, DecLcStTestUnlocked0);
    apply_reset();

    `DV_WAIT(cfg.sw_logger_vif.printed_log == "Waiting for LC transition done and reboot.",,
             50_000_000)
    // Wait for a large number of cycles to transit to RMA state.
    if (dest_dec_state == DecLcStRma) begin
      if (cfg.en_small_rma) begin
        `uvm_info(`gfn, "small_rma mode is enabled", UVM_LOW)
        enable_small_rma();
      end
    end

    wait_lc_status(LcTransitionSuccessful, 20_000_000);
    apply_reset();

    if (dest_dec_state == DecLcStRma) reload_flash_after_rma_transfer();

    // The following states will transfer twice to make sure LC_EXIT and RMA tokens are used.
    if (dest_dec_state inside {DecLcStProd, DecLcStDev}) begin
      `DV_WAIT(cfg.sw_logger_vif.printed_log == "Waiting for LC RMA transition done and reboot.",,
               50_000_000)

      // If small_rma enabled
      if (cfg.en_small_rma) begin
        `uvm_info(`gfn, "small_rma mode is enabled", UVM_LOW)
        enable_small_rma();
      end

      // Wait for a large number of cycles to transit to RMA state.
      wait_lc_status(LcTransitionSuccessful, 20_000_000);
      apply_reset();
      reload_flash_after_rma_transfer();
    end
  endtask

  // Reload flash bootstrap and reforce the sw symbols because RMA state wiped out flash.
  virtual task reload_flash_after_rma_transfer();
    bit [7:0] selected_dest_state[];
    selected_dest_state = {dest_dec_state};
    cfg.mem_bkdr_util_h[FlashBank0Data].load_mem_from_file(
        {cfg.sw_images[SwTypeTestSlotA], ".64.scr.vmem"});
    sw_symbol_backdoor_overwrite("kDestState", selected_dest_state);
  endtask
endclass
