// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package hmac_env_pkg;
  // dep packages
  import uvm_pkg::*;
  import top_pkg::*;
  import dv_utils_pkg::*;
  import csr_utils_pkg::*;
  import tl_agent_pkg::*;
  import cryptoc_dpi_pkg::*;
  import dv_base_reg_pkg::*;
  import cip_base_pkg::*;
  import test_vectors_pkg::*;
  import hmac_ral_pkg::*;
  import prim_sha2_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // local parameters and types
  parameter uint32 HMAC_MSG_FIFO_DEPTH_WR     = 32;
  parameter uint32 HMAC_MSG_FIFO_DEPTH_RD     = 16;
  parameter uint32 HMAC_MSG_FIFO_DEPTH_256    = 16;
  parameter uint32 HMAC_MSG_FIFO_DEPTH_512    = 32;
  parameter uint32 HMAC_MSG_FIFO_DEPTH_BYTES  = HMAC_MSG_FIFO_DEPTH_WR * 4;
  parameter uint32 HMAC_MSG_FIFO_SIZE         = 2048;
  parameter uint32 HMAC_MSG_FIFO_BASE         = 32'h1000;
  parameter uint32 HMAC_MSG_FIFO_LAST_ADDR    = HMAC_MSG_FIFO_BASE + HMAC_MSG_FIFO_SIZE - 1;
  parameter uint32 HMAC_BLK_SIZE_SHA2_256     = 512/8;  // Nb bytes
  parameter uint32 HMAC_BLK_SIZE_SHA2_384_512 = 1024/8; // Nb bytes
  // 48 cycles of hashing, 16 cycles to rd next 16 words, 1 cycle to update digest
  parameter uint32 HMAC_MSG_PROCESS_CYCLES   = 65;
  // 80 cycles for hmac key padding
  parameter uint32 HMAC_KEY_PROCESS_CYCLES   = 80;
  // 1 cycles to write a msg word to hmac_msg_fifo
  parameter uint32 HMAC_WR_WORD_CYCLE        = 1;

  parameter uint NUM_DIGESTS = 16;
  parameter uint NUM_KEYS    = 32;

  // alerts
  parameter uint NUM_ALERTS = 1;
  parameter string LIST_OF_ALERTS[] = {"fatal_fault"};

  // HMAC interrupt register indices
  typedef enum int {
    HmacDone          = 0,
    HmacMsgFifoEmpty  = 1,
    HmacErr           = 2
  } hmac_intr_e;

  // HMAC status register indices
  typedef enum int {
    HmacStaMsgFifoEmpty     = 0,
    HmacStaMsgFifoFull      = 1,
    HmacStaMsgFifoDepthLsb  = 4,
    HmacStaMsgFifoDepthMsb  = 9
  } hmac_sta_e;

  // HMAC cfg register indices
  typedef enum int {
    HmacEn        = 0,
    ShaEn         = 1,
    EndianSwap    = 2,
    DigestSwap    = 3,
    DigestSizeLsb = 4,
    DigestSizeMsb = 7,
    KeyLengthLsb  = 8,
    KeyLengthMsb  = 13
  } hmac_cfg_e;

  // HMAC cmd register indices
  typedef enum int {
    HashStart     = 0,
    HashProcess   = 1,
    HashStop      = 2,
    HashContinue  = 3
  } hmac_cmd_e;

  typedef enum int {
    NoError                    = 0,
    SwPushMsgWhenShaDisabled   = 1,
    SwHashStartWhenShaDisabled = 2,
    SwUpdateSecretKeyInProcess = 3,
    SwHashStartWhenActive      = 4,
    SwPushMsgWhenDisallowed    = 5,
    SwInvalidConfig            = 6
  } err_code_e;

  // Enum for the timing when issue wipe_secret CSR.
  typedef enum bit [2:0] {
    NoWipeSecret,
    WipeSecretBeforeKey,
    WipeSecretBeforeStart,
    WipeSecretBeforeProcess,
    WipeSecretBeforeDone
  } wipe_secret_req_e;

  typedef enum int {
    SameContext       = 0,
    DifferentContext  = 1
  } save_and_restore_e;

  typedef class hmac_env_cfg;
  typedef class hmac_env_cov;
  typedef cip_base_virtual_sequencer #(hmac_env_cfg, hmac_env_cov) hmac_virtual_sequencer;
  typedef virtual pins_if #(1) d2h_a_ready_vif;

  // functions
  function automatic int get_digest_index(string csr_name);
    case (csr_name)
      "digest_0": return 0;
      "digest_1": return 1;
      "digest_2": return 2;
      "digest_3": return 3;
      "digest_4": return 4;
      "digest_5": return 5;
      "digest_6": return 6;
      "digest_7": return 7;
      "digest_8": return 8;
      "digest_9": return 9;
      "digest_10": return 10;
      "digest_11": return 11;
      "digest_12": return 12;
      "digest_13": return 13;
      "digest_14": return 14;
      "digest_15": return 15;
      default: `uvm_fatal("get_digest_index", $sformatf("invalid digest csr name: %0s", csr_name))
    endcase
  endfunction

  function automatic int get_key_index(string csr_name);
    case (csr_name)
      "key_0": return 0;
      "key_1": return 1;
      "key_2": return 2;
      "key_3": return 3;
      "key_4": return 4;
      "key_5": return 5;
      "key_6": return 6;
      "key_7": return 7;
      "key_8": return 8;
      "key_9": return 9;
      "key_10": return 10;
      "key_11": return 11;
      "key_12": return 12;
      "key_13": return 13;
      "key_14": return 14;
      "key_15": return 15;
      "key_16": return 16;
      "key_17": return 17;
      "key_18": return 18;
      "key_19": return 19;
      "key_20": return 20;
      "key_21": return 21;
      "key_22": return 22;
      "key_23": return 23;
      "key_24": return 24;
      "key_25": return 25;
      "key_26": return 26;
      "key_27": return 27;
      "key_28": return 28;
      "key_29": return 29;
      "key_30": return 30;
      "key_31": return 31;
      default: `uvm_fatal("get_key_index", $sformatf("invalid key csr name: %0s", csr_name))
    endcase
  endfunction

  typedef virtual hmac_if hmac_vif;

  // package sources
  `include "hmac_env_cfg.sv"
  `include "hmac_env_cov.sv"
  `include "hmac_scoreboard.sv"
  `include "hmac_env.sv"
  `include "hmac_vseq_list.sv"
endpackage
