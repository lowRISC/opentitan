// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package kmac_env_pkg;
  // dep packages
  import uvm_pkg::*;
  import top_pkg::*;
  import dv_utils_pkg::*;
  import dv_lib_pkg::*;
  import dv_base_reg_pkg::*;
  import tl_agent_pkg::*;
  import str_utils_pkg::*;
  import test_vectors_pkg::*;
  import digestpp_dpi_pkg::*;
  import cip_base_pkg::*;
  import csr_utils_pkg::*;
  import push_pull_agent_pkg::*;
  import kmac_app_agent_pkg::*;
  import kmac_ral_pkg::*;
  import kmac_pkg::*;
  import keymgr_pkg::*;
  import key_sideload_agent_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters

  // max number of shares in design
  parameter int KMAC_NUM_SHARES = 2;

  parameter int KMAC_NUM_KEYS_PER_SHARE = 16;

  parameter int KMAC_NUM_PREFIX_WORDS = 11;

  // share1 of the 1600-bit KMAC state memory
  parameter bit [TL_AW-1:0] KMAC_STATE_SHARE0_BASE = 32'h400;
  parameter bit [TL_AW-1:0] KMAC_STATE_SHARE0_END  = 32'h4C7;

  // share2 of the 1600-bit KMAC state memory
  parameter bit [TL_AW-1:0] KMAC_STATE_SHARE1_BASE = 32'h500;
  parameter bit [TL_AW-1:0] KMAC_STATE_SHARE1_END  = 32'h5C7;

  // base and end addresses of the KAMC message FIFO.
  parameter bit [TL_AW-1:0] KMAC_FIFO_BASE = 32'h800;
  parameter bit [TL_AW-1:0] KMAC_FIFO_END = 32'hFFC;

  // width and depth of the msgfifo
  parameter int KMAC_FIFO_DEPTH = kmac_pkg::MsgFifoDepth;
  parameter int KMAC_FIFO_WIDTH = kmac_pkg::MsgWidth;

  parameter int KMAC_FIFO_WORDS_PER_ENTRY = KMAC_FIFO_WIDTH / TL_DW;

  parameter int KMAC_FIFO_BYTES_PER_ENTRY = KMAC_FIFO_WIDTH / 8;

  parameter int KMAC_FIFO_NUM_WORDS = KMAC_FIFO_DEPTH * KMAC_FIFO_WORDS_PER_ENTRY;

  parameter int KMAC_FIFO_NUM_BYTES = KMAC_FIFO_NUM_WORDS * 4;

  // Represents the max bit-width of some value to be encoded with either
  // `right_encode()` or `left_encode()`.
  parameter int MAX_ENCODE_WIDTH = 2040;

  // alerts
  parameter uint NUM_ALERTS = 2;
  parameter string LIST_OF_ALERTS[] = {"recov_operation_err", "fatal_fault_err"};

  parameter uint NUM_EDN = 1;

  /////////////////////////////
  // Timing Model Parameters //
  /////////////////////////////
  // Will include information related to both the keccak datapath and the entropy system,
  // as both directly relate to how many cycles a given hash operation will take

  // Existing parameters:
  //
  // sha3_pkg::MsgWidth = 64 -> width of internal datapath
  //
  // sha3_pkg::StateW = 1600 -> represents width of Keccak state

  // keccak datapath (lane) size
  localparam int W = sha3_pkg::StateW / 25;

  // log_2(W)
  localparam int L = $clog2(W);

  // interrupt types
  typedef enum int {
    KmacDone = 0,
    KmacFifoEmpty = 1,
    KmacErr = 2,
    KmacNumIntrs = 3
  } kmac_intr_e;

  // CFG csr bit positions
  typedef enum int {
    KmacEn = 0,
    KmacStrengthLSB = 1,
    KmacStrengthMSB = 3,
    KmacModeLSB = 4,
    KmacModeMSB = 5, KmacMsgEndian = 8,
    KmacStateEndian = 9,
    KmacSideload = 12,
    KmacEntropyModeLSB = 16,
    KmacEntropyModeMSB = 17,
    KmacFastEntropy = 19,
    KmacEntropyReady = 24,
    KmacErrProcessed = 25
  } kmac_cfg_e;

  // STATUS csr bit positions
  typedef enum int {
    KmacStatusSha3Idle = 0,
    KmacStatusSha3Absorb = 1,
    KmacStatusSha3Squeeze = 2,
    KmacStatusFifoDepthLSB = 8,
    KmacStatusFifoDepthMSB = 12,
    KmacStatusFifoEmpty = 14,
    KmacStatusFifoFull = 15
  } kmac_status_e;

  typedef enum int {
    KmacPrescaler = 0,
    KmacWaitTimer = 16
  } kmac_entropy_period_e;


  typedef enum int {
    KmacCmdIdx = 5,
    KmacEntropyReqIdx = 8,
    KmacHashCntClrIdx = 9
  } kmac_cmd_idx_e;

  typedef enum int {
    AppKeymgr,
    AppLc,
    AppRom
  } kmac_app_e;

  // state values of the App FSM
  typedef enum bit [9:0] {
    StIdle                  = 10'b1011011010,
    StAppCfg                = 10'b0001010000,
    StAppMsg                = 10'b0001011111,
    StAppOutLen             = 10'b1011001111,
    StAppProcess            = 10'b1000100110,
    StAppWait               = 10'b0010010110,
    StSw                    = 10'b0111111111,
    StKeyMgrErrKeyNotValid  = 10'b1001110100,
    StError                 = 10'b1101011101
  } kmac_app_st_e;

  // states of the error FSM
  typedef enum bit [2:0] {
    ErrStIdle,
    ErrStMsgFeed,
    ErrStProcessing,
    ErrStAbsorbed,
    ErrStSqueezing
  } kmac_err_st_e;

  typedef virtual key_sideload_if   sideload_vif;
  typedef virtual kmac_if           kmac_vif;

  // Helper functions that returns the KMAC key size in bytes/words/blocks
  function automatic int get_key_size_bytes(kmac_pkg::key_len_e len);
    case (len)
      Key128: return 16;
      Key192: return 24;
      Key256: return 32;
      Key384: return 48;
      Key512: return 64;
      default: `uvm_fatal("kmac_env_pkg", $sformatf("%0d is an invalid key length", len))
    endcase
  endfunction

  function automatic int get_key_size_words(kmac_pkg::key_len_e len);
    return (get_key_size_bytes(len) / 4);
  endfunction

  function automatic int get_key_size_blocks(kmac_pkg::key_len_e len);
    return (get_key_size_words(len) / 2);
  endfunction

  // package sources
  `include "kmac_env_cfg.sv"
  `include "kmac_env_cov.sv"
  `include "kmac_virtual_sequencer.sv"
  `include "kmac_scoreboard.sv"
  `include "kmac_env.sv"
  `include "kmac_vseq_list.sv"

endpackage
