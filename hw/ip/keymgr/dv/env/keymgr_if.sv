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

  // connect KDF interface for assertion check
  wire keymgr_pkg::kmac_data_req_t kmac_data_req;
  wire keymgr_pkg::kmac_data_rsp_t kmac_data_rsp;

  // indicate if check the key is same as expected or shouldn't match to any meaningful key
  bit is_kmac_key_good;
  bit is_hmac_key_good;
  bit is_aes_key_good;

  // when kmac sideload key is generated, kmac may be used to do other OP, but once the OP is done,
  // it should automatically switch back to sideload key
  bit is_kmac_sideload_avail;
  keymgr_env_pkg::key_shares_t kmac_sideload_key_shares;

  keymgr_env_pkg::key_shares_t keys_a_array[string][string];

  string msg_id = "keymgr_if";

  task automatic init();
    // This life cycle signal must be stable before
    // the key manager comes out of reset.
    // The power/reset manager ensures that
    // this sequencing is correct.
    keymgr_en = lc_ctrl_pkg::lc_tx_t'($urandom);

    // async delay as these signals are from different clock domain
    #($urandom_range(1000, 0) * 1ns);
    keymgr_en = lc_ctrl_pkg::On;
    keymgr_div = 64'h5CFBD765CE33F34E;
    otp_hw_cfg.data.device_id = 'hF0F0;
    otp_key = otp_ctrl_pkg::OTP_KEYMGR_KEY_DEFAULT;
    flash   = flash_ctrl_pkg::KEYMGR_FLASH_DEFAULT;
  endtask

  // reset local exp variables when reset is issued
  task automatic reset();
    kmac_key_exp = '0;
    hmac_key_exp = '0;
    aes_key_exp  = '0;
    is_kmac_key_good = 0;
    is_hmac_key_good = 0;
    is_aes_key_good  = 0;
    is_kmac_sideload_avail = 0;
  endtask

  // randomize otp, lc, flash input data
  task automatic drive_random_hw_input_data(int num_invalid_input = 0);
    lc_ctrl_pkg::lc_keymgr_div_t     local_keymgr_div;
    bit [keymgr_pkg::DevIdWidth-1:0] local_otp_device_id;
    otp_ctrl_pkg::otp_keymgr_key_t   local_otp_key;
    flash_ctrl_pkg::keymgr_flash_t   local_flash;

    // async delay as these signals are from different clock domain
    #($urandom_range(1000, 0) * 1ns);

    // randomize all data to be non all 0s or 1s
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(local_keymgr_div,
                                       !(local_keymgr_div inside {0, '1});, , msg_id)

    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(local_otp_device_id,
                                       !(local_otp_device_id inside {0, '1});, , msg_id)

    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(local_otp_key,
                                       local_otp_key.valid == 1;
                                       !(local_otp_key.key_share0 inside {0, '1});
                                       !(local_otp_key.key_share1 inside {0, '1});, , msg_id)

    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(local_flash,
                                       foreach (local_flash.seeds[i]) {
                                         !(local_flash.seeds[i] inside {0, '1});
                                       }, , msg_id)

    // make HW input to be all 0s or 1s
    repeat (num_invalid_input) begin
      randcase
        1: begin
          `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(local_keymgr_div,
                                             local_keymgr_div inside {0, '1};, , msg_id)
        end
        1: begin
          `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(local_otp_device_id,
                                             local_otp_device_id inside {0, '1};, , msg_id)
        end
        1: begin
          `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(local_otp_key,
                                             local_otp_key.valid == 1; // TODO this is tie to 1
                                             local_otp_key.key_share0 inside {0, '1} ||
                                             local_otp_key.key_share1 inside {0, '1};, , msg_id)
        end
        1: begin
          int idx = $urandom_range(0, flash_ctrl_pkg::NumSeeds - 1);
          `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(local_flash,
                                             local_flash.seeds[idx] inside {0, '1};, , msg_id)
        end
      endcase
    end

    keymgr_div = local_keymgr_div;
    otp_hw_cfg.data.device_id = local_otp_device_id;
    otp_key = local_otp_key;
    flash   = local_flash;
  endtask

  // update kmac key for comparison during KDF
  function automatic void update_kdf_key(keymgr_env_pkg::key_shares_t key_shares,
                                         keymgr_pkg::keymgr_working_state_e state,
                                         bit good_key = 1);

    kmac_key_exp <= '{1'b1, key_shares[0], key_shares[1]};
    is_kmac_key_good = good_key;
  endfunction

  // store internal key once it's available and use to compare if future OP is invalid
  function automatic void store_internal_key(keymgr_env_pkg::key_shares_t key_shares,
                                             keymgr_pkg::keymgr_working_state_e state);

    keys_a_array[state.name]["Internal"] = key_shares;
  endfunction

  // update sideload key for comparison
  // if it's good key, store it to compare for future invalid OP
  function automatic void update_sideload_key(keymgr_env_pkg::key_shares_t key_shares,
                                              keymgr_pkg::keymgr_working_state_e state,
                                              keymgr_pkg::keymgr_key_dest_e dest = keymgr_pkg::Kmac,
                                              bit good_key = 1);
    case (dest)
      keymgr_pkg::Kmac: begin
        kmac_key_exp             <= '{1'b1, key_shares[0], key_shares[1]};
        is_kmac_key_good         <= good_key;
        is_kmac_sideload_avail   <= 1;
        kmac_sideload_key_shares <= key_shares;
      end
      keymgr_pkg::Hmac: begin
        hmac_key_exp     <= '{1'b1, key_shares[0], key_shares[1]};
        is_hmac_key_good <= good_key;
      end
      keymgr_pkg::Aes: begin
        aes_key_exp     <= '{1'b1, key_shares[0], key_shares[1]};
        is_aes_key_good <= good_key;
      end
      default: `uvm_fatal("keymgr_if", $sformatf("Unexpect dest type %0s", dest.name))
    endcase

    if (good_key) keys_a_array[state.name][dest.name]  = key_shares;
  endfunction

  // if kmac sideload key is available, switch to it after an operation is completed
  // if not available, de-assert valid after done is asserted
  initial begin
    forever begin
      @(posedge clk);
      if (kmac_data_rsp.done) begin
        if (is_kmac_sideload_avail) begin
          kmac_key_exp <= '{1'b1, kmac_sideload_key_shares[0], kmac_sideload_key_shares[1]};
          is_kmac_key_good <= 1;
        end else begin
          kmac_key_exp.valid <= 0;
        end
      end // kmac_data_rsp.done
    end // forever
  end

  // check if key is invalid, it should not match to any of the meaningful keys
  initial begin
    fork
      forever begin
        @(posedge clk);
        if (!is_kmac_key_good) check_invalid_key(kmac_key, "KMAC");
      end
      forever begin
        @(posedge clk);
        if (!is_hmac_key_good) check_invalid_key(hmac_key, "HMAC");
      end
      forever begin
        @(posedge clk);
        if (!is_aes_key_good) check_invalid_key(aes_key, "AES");
      end
    join
  end

  function automatic void check_invalid_key(keymgr_pkg::hw_key_req_t act_key, string key_name);
    if (rst_n && act_key.valid) begin
      foreach (keys_a_array[i, j]) begin
        `DV_CHECK_NE({act_key.key_share1, act_key.key_share0}, keys_a_array[i][j],
            $sformatf("%s key at state %s from %s", key_name, i, j), , msg_id)
      end
    end
  endfunction

  `define KM_ASSERT(NAME, SEQ) \
    `ASSERT(NAME, SEQ, clk, !rst_n || keymgr_en != lc_ctrl_pkg::On)

  `KM_ASSERT(CheckKmacKey, is_kmac_key_good && kmac_key_exp.valid -> kmac_key == kmac_key_exp)

  `KM_ASSERT(CheckKmacKeyValid, kmac_key_exp.valid == kmac_key.valid)

  // TODO update hmac and aes checker later
  //`KM_ASSERT(HmacKeyStable, $stable(hmac_key_exp) |=> $stable(hmac_key))
  //`KM_ASSERT(HmacKeyUpdate, !$stable(hmac_key_exp) |=> hmac_key == hmac_key_exp)

  //`KM_ASSERT(AesKeyStable, $stable(aes_key_exp) |=> $stable(aes_key))
  //`KM_ASSERT(AesKeyUpdate, !$stable(aes_key_exp) |=> aes_key == aes_key_exp)

  `undef KM_ASSERT
endinterface
