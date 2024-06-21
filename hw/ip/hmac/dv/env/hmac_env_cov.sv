// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class hmac_env_cov extends cip_base_env_cov #(.CFG_T(hmac_env_cfg));
  `uvm_component_utils(hmac_env_cov)

  covergroup cfg_cg with function sample (bit [TL_DW-1:0] cfg);
    hmac_en: coverpoint cfg[HmacEn] {
      bins disabled = {1'b0};
      bins enabled  = {1'b1};
    }
    sha_en: coverpoint cfg[ShaEn] {
      bins disabled = {1'b0};
      bins enabled  = {1'b1};
    }
    endian_swap : coverpoint cfg[EndianSwap];
    digest_swap : coverpoint cfg[DigestSwap];
    key_swap    : coverpoint cfg[KeySwap];
    digest_size : coverpoint cfg[DigestSizeMsb:DigestSizeLsb] {
      bins sha2_256     = {4'h1};
      bins sha2_384     = {4'h2};
      bins sha2_512     = {4'h4};
      bins sha2_none    = {4'h8};
      bins sha2_invalid = digest_size with (!$onehot0(item));
    }
    key_length: coverpoint cfg[KeyLengthMsb:KeyLengthLsb] {
      bins key_128     = {6'h01};
      bins key_256     = {6'h02};
      bins key_384     = {6'h04};
      bins key_512     = {6'h08};
      bins key_1024    = {6'h10};
      bins key_none    = {6'h20};
      bins key_invalid = key_length with (!$onehot0(item));
    }
    cfg_cross: cross hmac_en, endian_swap, digest_swap, key_swap;
    hmac_dis_x_sha_en: cross hmac_en, sha_en {
      bins b0 = binsof(hmac_en.disabled) && binsof(sha_en.enabled);
    }
    key_x_digest_mismatch: cross key_length, digest_size {
      bins b0 = binsof(key_length.key_1024) && binsof(digest_size.sha2_256);
    }
    key_length_x_digest_size: cross key_length, digest_size;
  endgroup : cfg_cg

  covergroup status_cg with function sample (bit [TL_DW-1:0] sta, bit [TL_DW-1:0] cfg);
    hmac_en         : coverpoint cfg[HmacEn];
    endian_swap     : coverpoint cfg[EndianSwap];
    digest_swap     : coverpoint cfg[DigestSwap];
    key_swap        : coverpoint cfg[KeySwap];
    sta_fifo_empty  : coverpoint sta[HmacStaMsgFifoEmpty];
    sta_fifo_full   : coverpoint sta[HmacStaMsgFifoFull];
    sta_fifo_depth  : coverpoint sta[HmacStaMsgFifoDepthMsb:HmacStaMsgFifoDepthLsb] {
      bins fifo_depth[] = {[0:2^(HmacStaMsgFifoDepthMsb+1-HmacStaMsgFifoDepthLsb)-1]};
    }
    fifo_empty_cross: cross sta_fifo_empty, hmac_en, endian_swap, digest_swap, key_swap;
    fifo_full_cross : cross sta_fifo_full, hmac_en, endian_swap, digest_swap, key_swap;
    fifo_depth_cross: cross sta_fifo_depth, hmac_en, endian_swap, digest_swap, key_swap;
  endgroup : status_cg

  covergroup err_code_cg with function sample (bit [TL_DW-1:0] err_code);
    hmac_errors: coverpoint err_code {
      bins no_error                     = {NoError};
      // This error code is not used in this version. PR #13854.
      // bins push_msg_when_sha_disabled   = {SwPushMsgWhenShaDisabled};
      bins hash_start_when_sha_disabled = {SwHashStartWhenShaDisabled};
      bins update_secret_key_in_process = {SwUpdateSecretKeyInProcess};
      bins hash_start_when_active       = {SwHashStartWhenActive};
      bins push_msg_when_disallowed     = {SwPushMsgWhenDisallowed};
      bins invalid_config               = {SwInvalidConfig};
      illegal_bins illegalvalue         = default;
    }
  endgroup : err_code_cg

  covergroup msg_len_cg with function sample (logic [TL_DW-1:0] msg_len_lower,
                                              logic [TL_DW-1:0] msg_len_upper,
                                              logic [TL_DW-1:0] cfg          );
    hmac_en: coverpoint cfg[HmacEn];
    msg_len_lower_cp: coverpoint (msg_len_lower) {
      bins len_0         = {0};     // Empty message
      bins len_1         = {1};     // One byte message
      bins len_511       = {511};   // One block in SHA-2 256, -1 byte
      bins len_512       = {512};   // One block in SHA-2 256
      bins len_513       = {513};   // One block in SHA-2 256, +1 byte
      bins len_1023      = {1023};  // One block in SHA-2 384/512 or two in SHA-2 256, -1 byte
      bins len_1024      = {1024};  // One block in SHA-2 384/512 or two in SHA-2 256
      bins len_1025      = {1025};  // One block in SHA-2 384/512 or two in SHA-2 256, +1 byte
      bins len_2047      = {2047};  // Two blocks in SHA-2 384/512, -1 byte
      bins len_2048      = {2048};  // Two blocks in SHA-2 384/512
      bins len_2049      = {2049};  // Two blocks in SHA-2 384/512, +1 byte
      // Any others than the one defined above
      bins len_2_510     = {[2:510]};
      bins len_514_1022  = {[514:1022]};
      bins len_1026_2046 = {[1026:2046]};
      bins len_2050_plus = {[2050:$]};
    }
    // Ensure that message length upper register has been used once at least
    msg_len_upper_cp: coverpoint (msg_len_upper) {
      bins len_upper     = {[1:$]};
    }
    msg_len_lower_cross: cross hmac_en, msg_len_lower_cp;
    msg_len_upper_cross: cross hmac_en, msg_len_upper_cp;
  endgroup : msg_len_cg

  covergroup wr_config_during_hash_cg with function sample (logic wr_config_during_hash);
    cp: coverpoint wr_config_during_hash {bins true = {1'b1};}
  endgroup : wr_config_during_hash_cg

  covergroup wr_key_during_hash_cg with function sample (logic wr_key_during_hash);
    cp: coverpoint wr_key_during_hash {bins true = {1'b1};}
  endgroup : wr_key_during_hash_cg

  covergroup wr_key_during_sha_only_cg with function sample (logic wr_key_during_sha_only);
    cp: coverpoint wr_key_during_sha_only {bins true = {1'b1};}
  endgroup : wr_key_during_sha_only_cg

  covergroup wr_msg_during_hash_cg with function sample (logic wr_msg_during_hash);
    cp: coverpoint wr_msg_during_hash {bins true = {1'b1};}
  endgroup : wr_msg_during_hash_cg

  covergroup trig_rst_during_hash_cg with function sample (logic trig_rst_during_hash);
    cp: coverpoint trig_rst_during_hash {bins true = {1'b1};}
  endgroup : trig_rst_during_hash_cg

  covergroup rd_digest_during_hmac_en_cg with function sample (logic rd_digest_during_hmac_en);
    cp: coverpoint rd_digest_during_hmac_en {bins true = {1'b1};}
  endgroup : rd_digest_during_hmac_en_cg

  covergroup save_and_restore_cg with function sample (save_and_restore_e sar_ctxt,
                                                       bit [TL_DW-1:0] cfg);
    save_and_restore_cp : coverpoint sar_ctxt {
      bins same_context       = {SameContext};
      bins different_context  = {DifferentContext};
      bins stop_and_continue  = {StopAndContinue};
    }
    digest_size_cp : coverpoint cfg[DigestSizeMsb:DigestSizeLsb] {
      bins sha2_256     = {4'h1};
      bins sha2_384     = {4'h2};
      bins sha2_512     = {4'h4};
      // sha2_none and sha2_invalid are not valid here
    }
    sar_type_x_digest_size : cross save_and_restore_cp, digest_size_cp;
  endgroup : save_and_restore_cg

  function new(string name, uvm_component parent);
    super.new(name, parent);
    cfg_cg                      = new();
    status_cg                   = new();
    msg_len_cg                  = new();
    err_code_cg                 = new();
    wr_config_during_hash_cg    = new();
    wr_key_during_hash_cg       = new();
    wr_key_during_sha_only_cg   = new();
    wr_msg_during_hash_cg       = new();
    trig_rst_during_hash_cg     = new();
    rd_digest_during_hmac_en_cg = new();
    save_and_restore_cg         = new();
  endfunction : new
endclass
