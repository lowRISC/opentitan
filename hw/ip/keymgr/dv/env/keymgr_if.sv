// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// interface for input data from LC, OTP and flash
interface keymgr_if(input clk, input rst_n);

  import uvm_pkg::*;

  lc_ctrl_pkg::lc_tx_t            keymgr_en;
  lc_ctrl_pkg::lc_keymgr_div_t    keymgr_div;
  otp_ctrl_part_pkg::otp_hw_cfg_t otp_hw_cfg;
  otp_ctrl_pkg::otp_keymgr_key_t  otp_key;
  flash_ctrl_pkg::keymgr_flash_t  flash;

  keymgr_pkg::hw_key_req_t kmac_key;
  keymgr_pkg::hw_key_req_t hmac_key;
  keymgr_pkg::hw_key_req_t aes_key;

  keymgr_pkg::hw_key_req_t kmac_key_exp;
  keymgr_pkg::hw_key_req_t hmac_key_exp;
  keymgr_pkg::hw_key_req_t aes_key_exp;

  // indicate keymgr entered disabled directly. kmac_key are wiped, don't check output it
  bit direct_to_disabled;

  string msg_id = "keymgr_if";

  task automatic init();
    // async delay as these signals are from different clock domain
    #($urandom_range(1000, 0) * 1ns);
    keymgr_en = lc_ctrl_pkg::On;
    keymgr_div = 64'h5CFBD765CE33F34E;
    otp_hw_cfg.data.device_id = 'hF0F0;
    otp_key = otp_ctrl_pkg::OTP_KEYMGR_KEY_DEFAULT;
    flash   = flash_ctrl_pkg::KEYMGR_FLASH_DEFAULT;
    direct_to_disabled = 0;
  endtask

  // randomize otp, lc, flash input data
  task automatic drive_random_hw_input_data();
    lc_ctrl_pkg::lc_keymgr_div_t     local_keymgr_div;
    bit [keymgr_pkg::DevIdWidth-1:0] local_otp_device_id;
    otp_ctrl_pkg::otp_keymgr_key_t   local_otp_key;
    flash_ctrl_pkg::keymgr_flash_t   local_flash;

    // async delay as these signals are from different clock domain
    #($urandom_range(1000, 0) * 1ns);

    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(local_keymgr_div,
                                       !(local_keymgr_div inside {0, '1});, , msg_id)
    keymgr_div = local_keymgr_div;

    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(local_otp_device_id,
                                       !(local_otp_device_id inside {0, '1});, , msg_id)
    otp_hw_cfg.data.device_id = local_otp_device_id;

    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(local_otp_key,
                                       local_otp_key.valid == 1;
                                       !(local_otp_key.key_share0 inside {0, '1});
                                       !(local_otp_key.key_share1 inside {0, '1});, , msg_id)
    otp_key = local_otp_key;

    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(local_flash,
                                       foreach (local_flash.seeds[i]) {
                                         !(local_flash.seeds[i] inside {0, '1});
                                       }, , msg_id)
    flash   = local_flash;
  endtask

  task automatic update_exp_key(bit [keymgr_pkg::Shares-1:0][keymgr_pkg::KeyWidth-1:0] key_shares,
                                keymgr_pkg::keymgr_key_dest_e dest = keymgr_pkg::Kmac);
    case (dest)
      keymgr_pkg::Kmac: begin
        kmac_key_exp = '{1'b1, key_shares[0], key_shares[1]};
      end
      keymgr_pkg::Hmac: begin
        hmac_key_exp = '{1'b1, key_shares[0], key_shares[1]};
      end
      keymgr_pkg::Aes: begin
        aes_key_exp = '{1'b1, key_shares[0], key_shares[1]};
      end
      default: `uvm_fatal("keymgr_if", $sformatf("Unexpect dest type %0s", dest.name))
    endcase
  endtask

  task automatic enter_disabled_directly();
    direct_to_disabled = 1;
  endtask
  // TODO kmac_key only last until done signal is set. Fix this later
  //`ASSERT(KmacKeyStable, $stable(kmac_key_exp) && $stable(direct_to_disabled) |=> $stable(kmac_key),
  //    clk, !rst_n)
  //`ASSERT(KmacKeyUpdate, !$stable(kmac_key_exp) |=> kmac_key == kmac_key_exp,
  //    clk, !rst_n && !direct_to_disabled)

  `ASSERT(HmacKeyStable, $stable(hmac_key_exp) |=> $stable(hmac_key), clk, !rst_n)
  `ASSERT(HmacKeyUpdate, !$stable(hmac_key_exp) |=> hmac_key == hmac_key_exp, clk, !rst_n)

  `ASSERT(AesKeyStable, $stable(aes_key_exp) |=> $stable(aes_key), clk, !rst_n)
  `ASSERT(AesKeyUpdate, !$stable(aes_key_exp) |=> aes_key == aes_key_exp, clk, !rst_n)

endinterface
