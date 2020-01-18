// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package hmac_env_pkg;
  // dep packages
  import uvm_pkg::*;
  import top_pkg::*;
  import dv_utils_pkg::*;
  import csr_utils_pkg::*;
  import tl_agent_pkg::*;
  import alert_esc_agent_pkg::*;
  import cryptoc_dpi_pkg::*;
  import dv_lib_pkg::*;
  import cip_base_pkg::*;
  import test_vectors_pkg::*;
  import hmac_ral_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // local parameters and types
  // csr and mem total size for IP
  parameter uint   HMAC_ADDR_MAP_SIZE        = 4096;
  parameter uint32 HMAC_MSG_FIFO_DEPTH       = 16;
  parameter uint32 HMAC_MSG_FIFO_DEPTH_BYTES = HMAC_MSG_FIFO_DEPTH * 4;
  parameter uint32 HMAC_MSG_FIFO_SIZE        = 2048;
  parameter uint32 HMAC_MSG_FIFO_BASE        = 32'h800;
  parameter uint32 HMAC_MSG_FIFO_LAST_ADDR   = HMAC_MSG_FIFO_BASE + HMAC_MSG_FIFO_SIZE - 1;
  parameter uint32 HMAC_HASH_SIZE            = 64;
  // 48 cycles of hashing, 16 cycles to rd next 16 words, 1 cycle to update digest
  parameter uint32 HMAC_MSG_PROCESS_CYCLES   = 65;
  // 80 cycles for hmac key padding
  parameter uint32 HMAC_KEY_PROCESS_CYCLES   = 80;
  // 1 cycles to write a msg word to hmac_msg_fifo
  parameter uint32 HMAC_WR_WORD_CYCLE        = 1;

  typedef enum {
    HmacDone,
    HmacMsgFifoFull,
    HmacErr
  } hmac_intr_e;

  typedef enum {
    HmacStaMsgFifoEmpty,
    HmacStaMsgFifoFull,
    HmacStaMsgFifoDepth = 4
  } hmac_sta_e;

  typedef enum {
    HmacEn,
    ShaEn,
    EndianSwap,
    DigestSwap
  } hmac_cfg_e;

  typedef enum {
    HashStart,
    HashProcess
  } hmac_cmd_e;

  typedef enum {
    NoError,
    SwPushMsgWhenShaDisabled,
    SwHashStartWhenShaDisabled,
    SwUpdateSecretKeyInProcess
  } err_code_e;

  typedef class hmac_env_cfg;
  typedef class hmac_env_cov;
  typedef cip_base_virtual_sequencer #(hmac_env_cfg, hmac_env_cov) hmac_virtual_sequencer;
  typedef virtual pins_if #(1) d2h_a_ready_vif;

  // functions

  // package sources
  `include "hmac_env_cfg.sv"
  `include "hmac_env_cov.sv"
  `include "hmac_scoreboard.sv"
  `include "hmac_env.sv"
  `include "hmac_vseq_list.sv"
endpackage
