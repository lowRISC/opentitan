// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// interface for input data from LC, OTP and flash
interface keymgr_if(input clk, input rst_n);

  import uvm_pkg::*;

  keymgr_pkg::lc_data_t lc;
  keymgr_pkg::otp_data_t otp;
  otp_ctrl_pkg::otp_keymgr_key_t otp_key;
  flash_ctrl_pkg::keymgr_flash_t flash;

  keymgr_pkg::hw_key_req_t kmac_key;
  keymgr_pkg::hw_key_req_t hmac_key;
  keymgr_pkg::hw_key_req_t aes_key;

  keymgr_pkg::hw_key_req_t kmac_key_exp;
  keymgr_pkg::hw_key_req_t hmac_key_exp;
  keymgr_pkg::hw_key_req_t aes_key_exp;

  // indicate keymgr entered disabled directly. kmac_key are wiped, don't check output it
  bit direct_to_disabled;

  task automatic init();
    lc      = keymgr_pkg::LC_DATA_DEFAULT;
    otp     = keymgr_pkg::OTP_DATA_DEFAULT;
    otp_key = otp_ctrl_pkg::OTP_KEYMGR_KEY_DEFAULT;
    flash   = flash_ctrl_pkg::KEYMGR_FLASH_DEFAULT;
    direct_to_disabled = 0;
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
