// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package csrng_env_pkg;
  // dep packages
  import uvm_pkg::*;
  import top_pkg::*;
  import dv_utils_pkg::*;
  import push_pull_agent_pkg::*;
  import csrng_agent_pkg::*;
  import dv_lib_pkg::*;
  import tl_agent_pkg::*;
  import cip_base_pkg::*;
  import csr_utils_pkg::*;
  import csrng_ral_pkg::*;
  import aes_model_dpi_pkg::*;
  import prim_mubi_pkg::*;
  import entropy_src_pkg::*;
  import csrng_pkg::*;
  import lc_ctrl_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters
  parameter uint     NUM_HW_APPS             = 2;
  parameter uint     HW_APP0                 = 0;
  parameter uint     HW_APP1                 = 1;
  parameter uint     SW_APP                  = 2;
  parameter string   LIST_OF_ALERTS[]        = {"recov_alert","fatal_alert"};
  parameter uint     NUM_ALERTS              = 2;
  parameter uint     KEY_LEN                 = 256;
  parameter uint     BLOCK_LEN               = 128;
  parameter uint     CTR_LEN                 = 32;
  parameter uint     RSD_CTR_LEN             = 32;
  parameter uint     LC_HW_DEBUG_EN_ON_DATA  = 123456789;
  parameter uint     LC_HW_DEBUG_EN_OFF_DATA = 987654321;
  parameter uint     CSRNG_CMD_STS_WIDTH     = 3;

  // types
  typedef enum int {
    CmdReqDone = 0,
    EntropyReq = 1,
    HwInstExc  = 2,
    FifoErr    = 3
  } csrng_intr_e;

  typedef enum int {
    invalid_enable         = 0,
    invalid_sw_app_enable  = 1,
    invalid_read_int_state = 2
  } invalid_mubi_e;

  typedef enum int {
    sfifo_cmd_error      = 0,
    sfifo_genbits_error  = 1,
    sfifo_cmdreq_error   = 2,
    sfifo_rcstage_error  = 3,
    sfifo_keyvrc_error   = 4,
    sfifo_updreq_error   = 5,
    sfifo_bencreq_error  = 6,
    sfifo_bencack_error  = 7,
    sfifo_pdata_error    = 8,
    sfifo_final_error    = 9,
    sfifo_gbencack_error = 10,
    sfifo_grcstage_error = 11,
    sfifo_ggenreq_error  = 12,
    sfifo_gadstage_error = 13,
    sfifo_ggenbits_error = 14,
    sfifo_blkenc_error   = 15,
    cmd_stage_sm_error   = 16,
    main_sm_error        = 17,
    drbg_gen_sm_error    = 18,
    drbg_updbe_sm_error  = 19,
    drbg_updob_sm_error  = 20,
    aes_cipher_sm_error  = 21,
    cmd_gen_cnt_error    = 22,
    fifo_write_error     = 23,
    fifo_read_error      = 24,
    fifo_state_error     = 25
  } fatal_err_e;

  typedef enum int {
    // ERR_CODE
    sfifo_cmd_err           = 0,
    sfifo_genbits_err       = 1,
    sfifo_cmdreq_err        = 2,
    sfifo_rcstage_err       = 3,
    sfifo_keyvrc_err        = 4,
    sfifo_updreq_err        = 5,
    sfifo_bencreq_err       = 6,
    sfifo_bencack_err       = 7,
    sfifo_pdata_err         = 8,
    sfifo_final_err         = 9,
    sfifo_gbencack_err      = 10,
    sfifo_grcstage_err      = 11,
    sfifo_ggenreq_err       = 12,
    sfifo_gadstage_err      = 13,
    sfifo_ggenbits_err      = 14,
    sfifo_blkenc_err        = 15,
    cmd_stage_sm_err        = 16,
    main_sm_err             = 17,
    drbg_gen_sm_err         = 18,
    drbg_updbe_sm_err       = 19,
    drbg_updob_sm_err       = 20,
    aes_cipher_sm_err       = 21,
    cmd_gen_cnt_err         = 22,
    fifo_write_err          = 23,
    fifo_read_err           = 24,
    fifo_state_err          = 25,
    // ERR_CODE_TEST
    sfifo_cmd_err_test      = 26,
    sfifo_genbits_err_test  = 27,
    sfifo_cmdreq_err_test   = 28,
    sfifo_rcstage_err_test  = 29,
    sfifo_keyvrc_err_test   = 30,
    sfifo_updreq_err_test   = 31,
    sfifo_bencreq_err_test  = 32,
    sfifo_bencack_err_test  = 33,
    sfifo_pdata_err_test    = 34,
    sfifo_final_err_test    = 35,
    sfifo_gbencack_err_test = 36,
    sfifo_grcstage_err_test = 37,
    sfifo_ggenreq_err_test  = 38,
    sfifo_gadstage_err_test = 39,
    sfifo_ggenbits_err_test = 40,
    sfifo_blkenc_err_test   = 41,
    cmd_stage_sm_err_test   = 42,
    main_sm_err_test        = 43,
    drbg_gen_sm_err_test    = 44,
    drbg_updbe_sm_err_test  = 45,
    drbg_updob_sm_err_test  = 46,
    aes_cipher_sm_err_test  = 47,
    cmd_gen_cnt_err_test    = 48,
    fifo_write_err_test     = 49,
    fifo_read_err_test      = 50,
    fifo_state_err_test     = 51
  } err_code_e;

  typedef enum int {
    SFIFO_CMD_ERR      = 0,
    SFIFO_GENBITS_ERR  = 1,
    SFIFO_CMDREQ_ERR   = 2,
    SFIFO_RCSTAGE_ERR  = 3,
    SFIFO_KEYVRC_ERR   = 4,
    SFIFO_UPDREQ_ERR   = 5,
    SFIFO_BENCREQ_ERR  = 6,
    SFIFO_BENCACK_ERR  = 7,
    SFIFO_PDATA_ERR    = 8,
    SFIFO_FINAL_ERR    = 9,
    SFIFO_GBENCACK_ERR = 10,
    SFIFO_GRCSTAGE_ERR = 11,
    SFIFO_GGENREQ_ERR  = 12,
    SFIFO_GADSTAGE_ERR = 13,
    SFIFO_GGENBITS_ERR = 14,
    SFIFO_BLKENC_ERR   = 15,
    CMD_STAGE_SM_ERR   = 20,
    MAIN_SM_ERR        = 21,
    DRBG_GEN_SM_ERR    = 22,
    DRBG_UPDBE_SM_ERR  = 23,
    DRBG_UPDOB_SM_ERR  = 24,
    AES_CIPHER_SM_ERR  = 25,
    CMD_GEN_CNT_ERR    = 26,
    FIFO_WRITE_ERR     = 28,
    FIFO_READ_ERR      = 29,
    FIFO_STATE_ERR     = 30
  } err_code_bit_e;

  typedef enum int {
    ENABLE_FIELD_ALERT              = 0,
    SW_APP_ENABLE_FIELD_ALERT       = 1,
    READ_INT_STATE_FIELD_ALERT      = 2,
    ACMD_FLAG0_FIELD_ALERT          = 3,
    CS_BUS_CMP_ALERT                = 12,
    CMD_STAGE_INVALID_ACMD_ALERT    = 13,
    CMD_STAGE_INVALID_CMD_SEQ_ALERT = 14,
    CMD_STAGE_RESEED_CNT_ALERT      = 15
  } recov_alert_bit_e;

  typedef enum int {
    sfifo_blkenc   = 0,
    sfifo_ggenbits = 1,
    sfifo_gadstage = 2,
    sfifo_ggenreq  = 3,
    sfifo_grcstage = 4,
    sfifo_gbencack = 5,
    sfifo_final    = 6,
    sfifo_pdata    = 7,
    sfifo_bencack  = 8,
    sfifo_bencreq  = 9,
    sfifo_updreq   = 10,
    sfifo_keyvrc   = 11,
    sfifo_rcstage  = 12,
    sfifo_cmdreq   = 13,
    sfifo_genbits  = 14,
    sfifo_cmd      = 15
  } which_fifo_e;

  typedef enum int {
    fifo_write = 0,
    fifo_read  = 1,
    fifo_state = 2
  } which_fifo_err_e;

  typedef enum int {
    cmd_gen_cnt_sel  = 0,
    drbg_upd_cnt_sel = 1,
    drbg_gen_cnt_sel = 2
  } which_cnt_e;

  typedef enum int {
    fsm_sparse  = 0,
    fsm_redun   = 1,
    ctrl_sparse = 2,
    ctr_redun   = 3
  } which_aes_cm_e;

  // functions

  // package sources
  `include "csrng_env_cfg.sv"
  `include "csrng_env_cov.sv"
  `include "csrng_virtual_sequencer.sv"
  `include "csrng_scoreboard.sv"
  `include "csrng_env.sv"
  `include "csrng_vseq_list.sv"

endpackage
