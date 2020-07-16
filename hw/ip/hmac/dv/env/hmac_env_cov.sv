// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class hmac_env_cov extends cip_base_env_cov #(.CFG_T(hmac_env_cfg));
  `uvm_component_utils(hmac_env_cov)

  covergroup cfg_cg with function sample (bit [TL_DW-1:0] cfg);
    hmac_en:     coverpoint cfg[HmacEn];
    endian_swap: coverpoint cfg[EndianSwap];
    digest_swap: coverpoint cfg[DigestSwap];
    cfg_cross:   cross hmac_en, endian_swap, digest_swap;
  endgroup : cfg_cg

  covergroup status_cg with function sample (bit [TL_DW-1:0] sta, bit [TL_DW-1:0] cfg);
    hmac_en:          coverpoint cfg[HmacEn];
    endian_swap:      coverpoint cfg[EndianSwap];
    digest_swap:      coverpoint cfg[DigestSwap];
    sta_fifo_empty:   coverpoint sta[HmacStaMsgFifoEmpty];
    sta_fifo_full:    coverpoint sta[HmacStaMsgFifoFull];
    sta_fifo_depth:   coverpoint sta[HmacStaMsgFifoDepth + 4 : HmacStaMsgFifoDepth] {
      bins fifo_depth[] = {[0:16]};
    }
    fifo_empty_cross: cross sta_fifo_empty, hmac_en, endian_swap, digest_swap;
    fifo_full_cross:  cross sta_fifo_full, hmac_en, endian_swap, digest_swap;
    fifo_depth_cross: cross sta_fifo_depth, hmac_en, endian_swap, digest_swap;
  endgroup : status_cg

  covergroup err_code_cg with function sample (bit [TL_DW-1:0] err_code);
    hmac_errors: coverpoint err_code {
      bins no_error                     = {NoError};
      bins push_msg_when_sha_sisabled   = {SwPushMsgWhenShaDisabled};
      bins hash_start_when_sha_disabled = {SwHashStartWhenShaDisabled};
      bins update_secret_key_in_process = {SwUpdateSecretKeyInProcess};
      bins hash_start_when_active       = {SwHashStartWhenActive};
      bins push_msg_when_idle           = {SwPushMsgWhenIdle};
      illegal_bins illegalvalue         = default;
    }
  endgroup : err_code_cg

  covergroup msg_len_cg with function sample (bit [TL_DW-1:0] msg_len_lower, bit [TL_DW-1:0] cfg);
    hmac_en: coverpoint cfg[HmacEn];
    msg_len: coverpoint (msg_len_lower / 8) {
      bins len_0         = {0};
      bins len_1         = {1};
      bins len_256       = {256};
      bins len_257       = {257};
      bins len_512       = {512};
      bins len_513       = {513};
      bins len_768       = {768};
      bins len_769       = {769};
      bins len_1024      = {1024};
      bins len_1025      = {1025};
      bins len_1280      = {1280};
      bins len_1281      = {1281};
      bins len_1536      = {1536};
      bins len_1537      = {1537};
      bins len_1792      = {1792};
      bins len_1793      = {1793};
      bins len_2048      = {2048};
      bins len_2049      = {2049};
      bins len_2304      = {2304};
      bins len_2305      = {2305};
      bins len_2560      = {2560};
      bins len_2561      = {2561};
      bins len_2816      = {2816};
      bins len_2817      = {2817};
      bins len_3072      = {3072};
      bins len_3073      = {3073}; // up to 3000 for the most SW usage
      bins auto_lens[50] = {[1:10000]};
     }
    msg_len_cross: cross hmac_en, msg_len;
  endgroup : msg_len_cg

  function new(string name, uvm_component parent);
    super.new(name, parent);
    cfg_cg      = new();
    status_cg   = new();
    msg_len_cg  = new();
    err_code_cg = new();
  endfunction : new

endclass
