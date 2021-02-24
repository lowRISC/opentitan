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

  // connect EDN for assertion check
  wire edn_clk, edn_rst_n, edn_req, edn_ack;

  // keymgr_en is async, create a sync one for use in scb
  lc_ctrl_pkg::lc_tx_t keymgr_en_sync1, keymgr_en_sync2;

  // indicate if check the key is same as expected or shouldn't match to any meaningful key
  bit is_kmac_key_good;
  bit is_hmac_key_good;
  bit is_aes_key_good;

  // when kmac sideload key is generated, kmac may be used to do other OP, but once the OP is done,
  // it should automatically switch back to sideload key
  bit is_kmac_sideload_avail;
  keymgr_env_pkg::key_shares_t kmac_sideload_key_shares;

  keymgr_env_pkg::key_shares_t keys_a_array[string][string];

  // set this flag when design enters init state, edn req will start periodically
  bit start_edn_req;
  // keymgr will request edn twice for 64 bit data each time, use this to indicate if it's first or
  // second req. 0: wait for 1st req, 1: for 2nd
  bit edn_req_cnt;
  int edn_wait_cnt;
  int edn_interval;
  // synchronize req/ack from async domain
  bit edn_req_sync;
  bit edn_req_ack_sync;
  bit edn_req_ack_sync_done;

  // for scb to predict error and alert
  bit is_cmd_err;
  bit is_fsm_err;
  bit [2:0] force_cmds;

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
  function automatic void reset();
    kmac_key_exp = '0;
    hmac_key_exp = '0;
    aes_key_exp  = '0;
    is_kmac_key_good = 0;
    is_hmac_key_good = 0;
    is_aes_key_good  = 0;
    is_kmac_sideload_avail = 0;

    // edn related
    edn_interval  = 'h100;
    start_edn_req = 0;

    if (is_cmd_err) begin
      if (force_cmds[0]) release tb.dut.u_ctrl.adv_en_o;
      if (force_cmds[1]) release tb.dut.u_ctrl.id_en_o;
      if (force_cmds[2]) release tb.dut.u_ctrl.gen_en_o;
    end
    is_cmd_err = 0;
    is_fsm_err = 0;
  endfunction

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

  function automatic bit get_keymgr_en();
    return keymgr_en_sync2 === lc_ctrl_pkg::On;
  endfunction

  task automatic force_cmd_err();
    @(posedge clk);
    randcase
      // force more than one force_cmds are issued
      // TODO disable this case due to design issue #5363
      0: begin
        `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(force_cmds, $countones(force_cmds) > 1;, , msg_id)

        // these signals are wires, need force and then release at reset
        if (force_cmds[0]) force tb.dut.u_ctrl.adv_en_o = 1;
        if (force_cmds[1]) force tb.dut.u_ctrl.id_en_o  = 1;
        if (force_cmds[2]) force tb.dut.u_ctrl.gen_en_o = 1;
        @(posedge clk);
        if (force_cmds[0]) release tb.dut.u_ctrl.adv_en_o;
        if (force_cmds[1]) release tb.dut.u_ctrl.id_en_o;
        if (force_cmds[2]) release tb.dut.u_ctrl.gen_en_o;
        is_cmd_err = 1;
      end
      1: begin
        // Dynamic type in non-procedural context isn't allowed
        static reg [2:0] invalid_state;
        // 0-4 are illegal state
        `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(invalid_state, invalid_state > 4;, , msg_id)
        force tb.dut.u_kmac_if.state_q = invalid_state;
        @(posedge clk);
        release tb.dut.u_kmac_if.state_q;
        is_fsm_err = 1;
      end
    endcase
  endtask

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      keymgr_en_sync1 <= lc_ctrl_pkg::Off;
      keymgr_en_sync2 <= lc_ctrl_pkg::Off;
    end else begin
      keymgr_en_sync1 <= keymgr_en;
      // avoid race condtion in the driver
      keymgr_en_sync2 <= #1ps keymgr_en_sync1;
    end
  end

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
    if (rst_n && act_key.valid && !is_cmd_err && !is_fsm_err) begin
      foreach (keys_a_array[i, j]) begin
        `DV_CHECK_NE({act_key.key_share1, act_key.key_share0}, keys_a_array[i][j],
            $sformatf("%s key at state %s from %s", key_name, i, j), , msg_id)
      end
    end
  endfunction

  `define KM_ASSERT(NAME, SEQ) \
    `ASSERT(NAME, SEQ, clk, !rst_n || keymgr_en_sync2 != lc_ctrl_pkg::On || is_cmd_err || \
           is_fsm_err)

  `KM_ASSERT(CheckKmacKey, is_kmac_key_good && kmac_key_exp.valid -> kmac_key == kmac_key_exp)

  `KM_ASSERT(CheckKmacKeyValid, kmac_key_exp.valid == kmac_key.valid)

  // TODO update hmac and aes checker later
  //`KM_ASSERT(HmacKeyStable, $stable(hmac_key_exp) |=> $stable(hmac_key))
  //`KM_ASSERT(HmacKeyUpdate, !$stable(hmac_key_exp) |=> hmac_key == hmac_key_exp)

  //`KM_ASSERT(AesKeyStable, $stable(aes_key_exp) |=> $stable(aes_key))
  //`KM_ASSERT(AesKeyUpdate, !$stable(aes_key_exp) |=> aes_key == aes_key_exp)

  // for EDN assertion
  // sync req/ack to core clk domain
  always @(posedge edn_clk or negedge edn_rst_n) begin
    if (!edn_rst_n) begin
      edn_req_sync <= 0;
      edn_req_ack_sync <= 0;
    end else if (edn_req_ack_sync_done) begin
      edn_req_sync <= 0;
      edn_req_ack_sync <= 0;
    end else if (edn_req && !edn_req_sync) begin
      edn_req_sync <= 1;
    end else if (edn_req & edn_ack) begin
      edn_req_ack_sync <= 1;
    end
  end

  // use start_edn_req to skip checking 1st EDN req as it's triggered by advance cmd
  always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      edn_req_ack_sync_done <= 0;
      start_edn_req <= 0;
    end else if (edn_req_ack_sync && !edn_req_ack_sync_done) begin
      edn_req_ack_sync_done <= 1;
      start_edn_req <= 1;
    end else if (!edn_req_ack_sync) begin
      edn_req_ack_sync_done <= 0;
    end
  end

  always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      edn_wait_cnt <= 0;
    end else if (!edn_req_sync) begin
      edn_wait_cnt <= edn_wait_cnt + 1;
    end else begin
      edn_wait_cnt <= 0;
    end
  end

  initial begin
    forever begin
      wait(rst_n === 1);
      edn_req_cnt <= 0;
      `DV_SPINWAIT_EXIT(forever begin
                          @(negedge edn_req_ack_sync_done);
                          edn_req_cnt <= edn_req_cnt + 1;
                        end,
                        wait(!rst_n), , msg_id)
    end
  end

  // consider async handshaking and a few cycles to start the req. allow no more than 20 tolerance
  // error on the cnt
  `ASSERT(CheckEdn1stReq, $rose(edn_req_sync) && edn_req_cnt == 0 && start_edn_req |->
          edn_wait_cnt - edn_interval < 20, clk, !rst_n)

  `ASSERT(CheckEdn2ndReq, $fell(edn_req_sync) && edn_req_cnt == 1 |-> edn_wait_cnt < 20,
          clk, !rst_n)

  `undef KM_ASSERT
endinterface
