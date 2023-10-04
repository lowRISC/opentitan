// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package edn_env_pkg;
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
  import edn_ral_pkg::*;
  import prim_mubi_pkg::*;
  import edn_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters
  parameter uint     MIN_NUM_ENDPOINTS = 1;
  parameter uint     MAX_NUM_ENDPOINTS = 7;
  parameter string   LIST_OF_ALERTS[]  = {"recov_alert","fatal_alert"};
  parameter uint     NUM_ALERTS        = 2;

  // types
  typedef enum int {
    CmdReqDone  = 0,
    FifoErr     = 1,
    NumEdnIntr  = 2
  } edn_intr_e;

  typedef enum int {
    AutoReqMode = 1,
    BootReqMode = 2,
    SwMode      = 3
  } hw_req_mode_e;

  typedef enum int {
    BootIns = 1,
    BootGen = 2,
    AutoGen = 3,
    AutoRes = 4,
    Sw      = 5
  } cmd_type_e;

  typedef enum int {
    invalid_edn_enable    = 0,
    invalid_boot_req_mode = 1,
    invalid_auto_req_mode = 2,
    invalid_cmd_fifo_rst  = 3
  } invalid_mubi_e;

  typedef enum int {
    sfifo_rescmd_error    = 0,
    sfifo_gencmd_error    = 1,
    edn_ack_sm_error      = 2,
    edn_main_sm_error     = 3,
    edn_cntr_error        = 4
  } fatal_err_e;

  typedef enum int {
    sfifo_rescmd_err      = 0,
    sfifo_gencmd_err      = 1,
    sfifo_output_err      = 2,
    edn_ack_sm_err        = 3,
    edn_main_sm_err       = 4,
    edn_cntr_err          = 5,
    fifo_write_err        = 6,
    fifo_read_err         = 7,
    fifo_state_err        = 8,
    sfifo_rescmd_err_test = 9,
    sfifo_gencmd_err_test = 10,
    sfifo_output_err_test = 11,
    edn_ack_sm_err_test   = 12,
    edn_main_sm_err_test  = 13,
    edn_cntr_err_test     = 14,
    fifo_write_err_test   = 15,
    fifo_read_err_test    = 16,
    fifo_state_err_test   = 17
  } err_code_e;

  typedef enum int {
    EdnSfifoRescmdErrTest = 0,
    EdnSfifoGencmdErrTest = 1,
    EdnSfifoOutputErrTest = 2,
    EdnAckSmErrTest       = 20,
    EdnMainSmErrTest      = 21,
    EdnCntrErrTest        = 22,
    EdnFifoWriteErrTest   = 28,
    EdnFifoReadErrTest    = 29,
    EdnFifoStateErrTest   = 30
  } err_code_test_e;

  typedef enum int {
    edn_enable_field_alert    = 0,
    boot_req_mode_field_alert = 1,
    auto_req_mode_field_alert = 2,
    cmd_fifo_rst_field_alert  = 3,
    edn_bus_cmp_alert         = 12
  } recov_alert_bit_e;

  typedef enum int {
    sfifo_rescmd = 0,
    sfifo_gencmd = 1
  } which_fifo_e;

  typedef enum int {
    fifo_write_error = 0,
    fifo_read_error  = 1,
    fifo_state_error = 2
  } which_fifo_err_e;

  // package sources
  `include "edn_env_cfg.sv"
  `include "edn_env_cov.sv"
  `include "edn_virtual_sequencer.sv"
  `include "edn_scoreboard.sv"
  `include "edn_env.sv"
  `include "edn_vseq_list.sv"

endpackage
