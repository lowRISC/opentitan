// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: csrng core module
//


module csrng_core import csrng_pkg::*; #(
  parameter aes_pkg::sbox_impl_e SBoxImpl = aes_pkg::SBoxImplLut,
  parameter int NumHwApps = 2,
  parameter cs_keymgr_div_t RndCnstCsKeymgrDivNonProduction = CsKeymgrDivWidth'(0),
  parameter cs_keymgr_div_t RndCnstCsKeymgrDivProduction = CsKeymgrDivWidth'(0)
) (
  input logic                                     clk_i,
  input logic                                     rst_ni,

  input  csrng_reg_pkg::csrng_reg2hw_t            reg2hw,
  output csrng_reg_pkg::csrng_hw2reg_t            hw2reg,

  // OTP Interface
  input  prim_mubi_pkg::mubi8_t                   otp_en_csrng_sw_app_read_i,

  // Lifecycle broadcast inputs
  input  lc_ctrl_pkg::lc_tx_t                     lc_hw_debug_en_i,

  // Entropy Interface
  output entropy_src_pkg::entropy_src_hw_if_req_t entropy_src_hw_if_o,
  input  entropy_src_pkg::entropy_src_hw_if_rsp_t entropy_src_hw_if_i,

  // Entropy Interface
  input  entropy_src_pkg::cs_aes_halt_req_t       cs_aes_halt_i,
  output entropy_src_pkg::cs_aes_halt_rsp_t       cs_aes_halt_o,

  // Application Interfaces
  input  csrng_req_t [NumHwApps-1:0]              csrng_cmd_i,
  output csrng_rsp_t [NumHwApps-1:0]              csrng_cmd_o,

  // Alerts
  output logic                                    recov_alert_test_o,
  output logic                                    fatal_alert_test_o,
  output logic                                    recov_alert_o,
  output logic                                    fatal_alert_o,

  // Interrupts
  output logic                                    intr_cs_cmd_req_done_o,
  output logic                                    intr_cs_entropy_req_o,
  output logic                                    intr_cs_hw_inst_exc_o,
  output logic                                    intr_cs_fatal_err_o
);

  import csrng_reg_pkg::*;

  import prim_mubi_pkg::mubi4_t;
  import prim_mubi_pkg::mubi4_test_true_strict;
  import prim_mubi_pkg::mubi4_test_invalid;

  localparam int unsigned ADataDepthClog = $clog2(CmdMaxClen) + 1;
  localparam int unsigned CsEnableCopies = 51;
  localparam int unsigned LcHwDebugCopies = 1;
  localparam int unsigned Flag0Copies = 3;

  // signals
  // interrupt signals
  logic                        event_cs_cmd_req_done;
  logic                        event_cs_entropy_req;
  logic                        event_cs_hw_inst_exc;
  logic                        event_cs_fatal_err;
  logic [CsEnableCopies-1:1]   cs_enable_fo;
  logic [Flag0Copies-1:0]      flag0_fo;
  logic                        acmd_flag0_pfa;
  logic                        cs_enable_pfa;
  logic                        sw_app_enable;
  logic                        sw_app_enable_pfe;
  logic                        sw_app_enable_pfa;
  logic                        read_int_state;
  logic                        read_int_state_pfe;
  logic                        read_int_state_pfa;
  logic                        fips_force_enable;
  logic                        fips_force_enable_pfe;
  logic                        fips_force_enable_pfa;
  logic                        recov_alert_event;
  logic                        acmd_avail;
  logic                        acmd_sop;
  logic                        acmd_mop;
  logic                        acmd_eop;

  logic                        state_db_wr_vld;
  csrng_core_data_t            state_db_wr_data;
  csrng_cmd_sts_e              state_db_wr_sts;
  csrng_state_t                state_db_rd_data;

  logic [CmdBusWidth-1:0]      acmd_bus;
  acmd_e                       acmd_hold;

  logic [SeedLen-1:0]          packer_adata;
  logic [ADataDepthClog-1:0]   packer_adata_depth;
  logic                        packer_adata_pop;
  logic                        packer_adata_clr;
  logic [SeedLen-1:0]          seed_diversification;

  logic                        cmd_entropy_req;
  logic                        cmd_entropy_avail;
  logic                        cmd_entropy_fips;
  logic [SeedLen-1:0]          cmd_entropy;

  logic                        ctr_drbg_cmd_rsp_vld;
  logic                        ctr_drbg_cmd_rsp_rdy;
  csrng_core_data_t            ctr_drbg_cmd_rsp_data;
  logic                        ctr_drbg_cmd_rsp_glast;

  logic                        ctr_drbg_cmd_req_vld;
  logic                        ctr_drbg_cmd_req_rdy;
  csrng_core_data_t            ctr_drbg_cmd_req_data;

  logic                        ctr_drbg_gen_req_vld;
  logic                        ctr_drbg_gen_req_rdy;

  logic                        ctr_drbg_gen_rsp_vld;
  logic                        ctr_drbg_gen_rsp_rdy;
  csrng_core_data_t            ctr_drbg_gen_rsp_data;
  logic [BlkLen-1:0]           ctr_drbg_gen_rsp_bits;
  csrng_cmd_sts_e              ctr_drbg_gen_rsp_sts;

  logic                        state_db_sts_ack;
  csrng_cmd_sts_e              state_db_sts_sts;
  logic [InstIdWidth-1:0]      state_db_sts_id;

  logic                        acmd_accept;
  logic                        main_sm_cmd_vld;
  logic                        clr_adata_packer;

  logic                        ctr_drbg_upd_sfifo_final_err_sum;
  logic [2:0]                  ctr_drbg_upd_sfifo_final_err;
  logic                        ctr_drbg_gen_sfifo_gbencack_err_sum;
  logic [2:0]                  ctr_drbg_gen_sfifo_gbencack_err;
  logic                        ctr_drbg_gen_sfifo_grcstage_err_sum;
  logic [2:0]                  ctr_drbg_gen_sfifo_grcstage_err;
  logic                        ctr_drbg_gen_sfifo_gadstage_err_sum;
  logic [2:0]                  ctr_drbg_gen_sfifo_gadstage_err;
  logic                        ctr_drbg_gen_sfifo_ggenbits_err_sum;
  logic [2:0]                  ctr_drbg_gen_sfifo_ggenbits_err;
  logic                        block_encrypt_sfifo_cmdid_err_sum;
  logic [2:0]                  block_encrypt_sfifo_cmdid_err;
  logic                        fifo_write_err_sum;
  logic                        fifo_read_err_sum;
  logic                        fifo_status_err_sum;

  logic                        cmd_gen_cnt_err_sum;
  logic                        cmd_stage_sm_err_sum;
  logic                        main_sm_err_sum;
  logic                        cs_main_sm_err;
  logic [MainSmStateWidth-1:0] cs_main_sm_state;
  logic                        drbg_cmd_sm_err_sum;
  logic                        drbg_cmd_sm_err;
  logic                        drbg_gen_sm_err_sum;
  logic                        drbg_gen_sm_err;
  logic                        drbg_updbe_sm_err_sum;
  logic                        drbg_updbe_sm_err;
  logic                        drbg_updob_sm_err_sum;
  logic                        drbg_updob_sm_err;
  logic                        block_encrypt_sm_err_sum;
  logic                        block_encrypt_sm_err;

  // blk encrypt arbiter
  // request path
  logic                        upd_benc_req_vld;
  logic                        upd_benc_req_rdy;
  csrng_benc_data_t            upd_benc_req_data;

  logic                        gen_benc_req_vld;
  logic                        gen_benc_req_rdy;
  csrng_benc_data_t            gen_benc_req_data;

  logic                        block_encrypt_req_vld;
  logic                        block_encrypt_req_rdy;
  csrng_benc_data_t            block_encrypt_req_data;

  // response path
  logic                        upd_benc_rsp_vld;
  logic                        upd_benc_rsp_rdy;

  logic                        gen_benc_rsp_vld;
  logic                        gen_benc_rsp_rdy;

  logic                        block_encrypt_rsp_vld;
  logic                        block_encrypt_rsp_rdy;
  csrng_benc_data_t            block_encrypt_rsp_data;

  // update unit arbiter
  // request path
  logic                        cmd_upd_req_vld;
  logic                        cmd_upd_req_rdy;
  csrng_upd_data_t             cmd_upd_req_data;

  logic                        gen_upd_req_vld;
  logic                        gen_upd_req_rdy;
  csrng_upd_data_t             gen_upd_req_data;

  logic                        upd_arb_req_vld;
  logic                        upd_arb_req_rdy;
  csrng_upd_data_t             upd_arb_req_data;

  // response path
  logic                        cmd_upd_rsp_vld;
  logic                        cmd_upd_rsp_rdy;

  logic                        gen_upd_rsp_vld;
  logic                        gen_upd_rsp_rdy;

  logic                        upd_rsp_vld;
  logic                        upd_rsp_rdy;
  csrng_upd_data_t             upd_rsp_data;


  logic [2:0]                  cmd_stage_sfifo_cmd_err[NumApps];
  logic [NumApps-1:0]          cmd_stage_sfifo_cmd_err_sum;
  logic [NumApps-1:0]          cmd_stage_sfifo_cmd_err_wr;
  logic [NumApps-1:0]          cmd_stage_sfifo_cmd_err_rd;
  logic [NumApps-1:0]          cmd_stage_sfifo_cmd_err_st;
  logic [2:0]                  cmd_stage_sfifo_genbits_err[NumApps];
  logic [NumApps-1:0]          cmd_stage_sfifo_genbits_err_sum;
  logic [NumApps-1:0]          cmd_stage_sfifo_genbits_err_wr;
  logic [NumApps-1:0]          cmd_stage_sfifo_genbits_err_rd;
  logic [NumApps-1:0]          cmd_stage_sfifo_genbits_err_st;
  logic [NumApps-1:0]          cmd_gen_cnt_err;
  logic [NumApps-1:0]          cmd_stage_sm_err;
  logic                        ctr_drbg_upd_v_ctr_err;
  logic                        ctr_drbg_gen_v_ctr_err;

  logic [NumApps-1:0]          cmd_stage_vld;
  logic [InstIdWidth-1:0]      cmd_stage_shid[NumApps];
  logic [CmdBusWidth-1:0]      cmd_stage_bus[NumApps];
  logic [NumApps-1:0]          cmd_stage_rdy;
  logic [NumApps-1:0]          cmd_arb_req;
  logic [NumApps-1:0]          cmd_arb_gnt;
  logic [$clog2(NumApps)-1:0]  cmd_arb_idx;
  logic [NumApps-1:0]          cmd_arb_sop;
  logic [NumApps-1:0]          cmd_arb_mop;
  logic [NumApps-1:0]          cmd_arb_eop;
  logic [CmdBusWidth-1:0]      cmd_arb_bus[NumApps];
  logic [NumApps-1:0]          cmd_core_ack;
  csrng_cmd_sts_e [NumApps-1:0]cmd_core_ack_sts;
  logic [NumApps-1:0]          cmd_stage_ack;
  csrng_cmd_sts_e [NumApps-1:0]cmd_stage_ack_sts;
  logic [NumApps-1:0]          genbits_core_vld;
  logic [BlkLen-1:0]           genbits_core_bus[NumApps];
  logic [NumApps-1:0]          genbits_core_fips;
  logic [NumApps-1:0]          genbits_stage_vld;
  logic [NumApps-1:0]          genbits_stage_fips;
  logic [BlkLen-1:0]           genbits_stage_bus[NumApps];
  logic [NumApps-1:0]          genbits_stage_rdy;
  logic                        genbits_stage_vldo_sw;
  logic                        genbits_stage_bus_rd_sw;
  logic [31:0]                 genbits_stage_bus_sw;
  logic                        genbits_stage_fips_sw;

  logic [15:0]                 hw_exception_sts;
  logic [LcHwDebugCopies-1:0]  lc_hw_debug_on_fo;
  logic                        state_db_reg_read_en;

  logic [30:0]                 err_code_test_bit;
  logic                        ctr_drbg_upd_es_ack;
  logic                        ctr_drbg_gen_es_ack;
  logic                        block_encrypt_quiet;

  logic                        cs_rdata_capt_vld;
  logic                        cs_bus_cmp_alert;
  logic                        cmd_rdy;
  logic [NumApps-1:0]          invalid_cmd_seq_alert;
  logic [NumApps-1:0]          invalid_acmd_alert;
  logic [NumApps-1:0]          reseed_cnt_alert;
  logic                        sw_sts_ack;
  logic [1:0]                  otp_sw_app_read_en;

  logic [NumApps-1:0][31:0]    reseed_counter;

  prim_mubi_pkg::mubi8_t                [1:0] otp_sw_app_read_en_mubi;
  prim_mubi_pkg::mubi4_t [CsEnableCopies-1:0] mubi_cs_enable_fanout;
  prim_mubi_pkg::mubi4_t    [Flag0Copies-1:0] mubi_flag0_fanout;

  // flops
  acmd_e                acmd_q, acmd_d;
  logic [3:0]           shid_q, shid_d;
  logic                 gen_last_q, gen_last_d;
  mubi4_t               flag0_q, flag0_d;
  logic [NumAppsLg-1:0] cmd_arb_idx_q, cmd_arb_idx_d;
  logic                 genbits_stage_fips_sw_q, genbits_stage_fips_sw_d;
  acmd_e                cmd_req_ccmd_dly_q, cmd_req_ccmd_dly_d;
  logic                 cs_aes_halt_q, cs_aes_halt_d;
  logic [SeedLen-1:0]   entropy_src_seed_q, entropy_src_seed_d;
  logic                 entropy_src_fips_q, entropy_src_fips_d;
  logic [63:0]          cs_rdata_capt_q, cs_rdata_capt_d;
  logic                 cs_rdata_capt_vld_q, cs_rdata_capt_vld_d;
  logic                 sw_rdy_sts_q, sw_rdy_sts_d;
  logic                 sw_sts_ack_q, sw_sts_ack_d;
  logic [NumApps-1:0]   reseed_cnt_reached_q, reseed_cnt_reached_d;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      acmd_q                  <= INV;
      shid_q                  <= '0;
      gen_last_q              <= '0;
      flag0_q                 <= prim_mubi_pkg::MuBi4False;
      cmd_arb_idx_q           <= '0;
      genbits_stage_fips_sw_q <= '0;
      cmd_req_ccmd_dly_q      <= INV;
      cs_aes_halt_q           <= '0;
      entropy_src_seed_q      <= '0;
      entropy_src_fips_q      <= '0;
      cs_rdata_capt_q         <= '0;
      cs_rdata_capt_vld_q     <= '0;
      sw_rdy_sts_q            <= '0;
      sw_sts_ack_q            <= '0;
      reseed_cnt_reached_q    <= '0;
    end else begin
      acmd_q                  <= acmd_d;
      shid_q                  <= shid_d;
      gen_last_q              <= gen_last_d;
      flag0_q                 <= flag0_d;
      cmd_arb_idx_q           <= cmd_arb_idx_d;
      genbits_stage_fips_sw_q <= genbits_stage_fips_sw_d;
      cmd_req_ccmd_dly_q      <= cmd_req_ccmd_dly_d;
      cs_aes_halt_q           <= cs_aes_halt_d;
      entropy_src_seed_q      <= entropy_src_seed_d;
      entropy_src_fips_q      <= entropy_src_fips_d;
      cs_rdata_capt_q         <= cs_rdata_capt_d;
      cs_rdata_capt_vld_q     <= cs_rdata_capt_vld_d;
      sw_rdy_sts_q            <= sw_rdy_sts_d;
      sw_sts_ack_q            <= sw_sts_ack_d;
      reseed_cnt_reached_q    <= reseed_cnt_reached_d;
    end
  end

  //--------------------------------------------
  // instantiate interrupt hardware primitives
  //--------------------------------------------
  // All TLUL interrupts are collect in the section.

  prim_intr_hw #(
    .Width(1)
  ) u_intr_hw_cs_cmd_req_done (
    .clk_i                 (clk_i),
    .rst_ni                (rst_ni),
    .event_intr_i          (event_cs_cmd_req_done),
    .reg2hw_intr_enable_q_i(reg2hw.intr_enable.cs_cmd_req_done.q),
    .reg2hw_intr_test_q_i  (reg2hw.intr_test.cs_cmd_req_done.q),
    .reg2hw_intr_test_qe_i (reg2hw.intr_test.cs_cmd_req_done.qe),
    .reg2hw_intr_state_q_i (reg2hw.intr_state.cs_cmd_req_done.q),
    .hw2reg_intr_state_de_o(hw2reg.intr_state.cs_cmd_req_done.de),
    .hw2reg_intr_state_d_o (hw2reg.intr_state.cs_cmd_req_done.d),
    .intr_o                (intr_cs_cmd_req_done_o)
  );

  prim_intr_hw #(
    .Width(1)
  ) u_intr_hw_cs_entropy_req (
    .clk_i                 (clk_i),
    .rst_ni                (rst_ni),
    .event_intr_i          (event_cs_entropy_req),
    .reg2hw_intr_enable_q_i(reg2hw.intr_enable.cs_entropy_req.q),
    .reg2hw_intr_test_q_i  (reg2hw.intr_test.cs_entropy_req.q),
    .reg2hw_intr_test_qe_i (reg2hw.intr_test.cs_entropy_req.qe),
    .reg2hw_intr_state_q_i (reg2hw.intr_state.cs_entropy_req.q),
    .hw2reg_intr_state_de_o(hw2reg.intr_state.cs_entropy_req.de),
    .hw2reg_intr_state_d_o (hw2reg.intr_state.cs_entropy_req.d),
    .intr_o                (intr_cs_entropy_req_o)
  );

  prim_intr_hw #(
    .Width(1)
  ) u_intr_hw_cs_hw_inst_exc (
    .clk_i                 (clk_i),
    .rst_ni                (rst_ni),
    .event_intr_i          (event_cs_hw_inst_exc),
    .reg2hw_intr_enable_q_i(reg2hw.intr_enable.cs_hw_inst_exc.q),
    .reg2hw_intr_test_q_i  (reg2hw.intr_test.cs_hw_inst_exc.q),
    .reg2hw_intr_test_qe_i (reg2hw.intr_test.cs_hw_inst_exc.qe),
    .reg2hw_intr_state_q_i (reg2hw.intr_state.cs_hw_inst_exc.q),
    .hw2reg_intr_state_de_o(hw2reg.intr_state.cs_hw_inst_exc.de),
    .hw2reg_intr_state_d_o (hw2reg.intr_state.cs_hw_inst_exc.d),
    .intr_o                (intr_cs_hw_inst_exc_o)
  );

  prim_intr_hw #(
    .Width(1)
  ) u_intr_hw_cs_fatal_err (
    .clk_i                 (clk_i),
    .rst_ni                (rst_ni),
    .event_intr_i          (event_cs_fatal_err),
    .reg2hw_intr_enable_q_i(reg2hw.intr_enable.cs_fatal_err.q),
    .reg2hw_intr_test_q_i  (reg2hw.intr_test.cs_fatal_err.q),
    .reg2hw_intr_test_qe_i (reg2hw.intr_test.cs_fatal_err.qe),
    .reg2hw_intr_state_q_i (reg2hw.intr_state.cs_fatal_err.q),
    .hw2reg_intr_state_de_o(hw2reg.intr_state.cs_fatal_err.de),
    .hw2reg_intr_state_d_o (hw2reg.intr_state.cs_fatal_err.d),
    .intr_o                (intr_cs_fatal_err_o)
  );

  // Counter and FSM errors are structural errors and are always active regardless of the
  // functional state. main_sm_err_sum is not included here to prevent some tools from
  // inferring combo loops. However, to include the state machine error for testing,
  // we use the error code test bit (index 21) directly.
  logic fatal_loc_events;
  assign fatal_loc_events = cmd_gen_cnt_err_sum ||
                            cmd_stage_sm_err_sum ||
                            drbg_cmd_sm_err_sum ||
                            drbg_gen_sm_err_sum ||
                            drbg_updbe_sm_err_sum ||
                            drbg_updob_sm_err_sum ||
                            block_encrypt_sm_err_sum ||
                            err_code_test_bit[21];

  // set the interrupt sources
  assign event_cs_fatal_err = (cs_enable_fo[1]  && (
         (|cmd_stage_sfifo_cmd_err_sum) ||
         (|cmd_stage_sfifo_genbits_err_sum) ||
         ctr_drbg_upd_sfifo_final_err_sum ||
         ctr_drbg_gen_sfifo_gbencack_err_sum ||
         ctr_drbg_gen_sfifo_grcstage_err_sum ||
         ctr_drbg_gen_sfifo_gadstage_err_sum ||
         ctr_drbg_gen_sfifo_ggenbits_err_sum ||
         block_encrypt_sfifo_cmdid_err_sum ||
         fifo_write_err_sum ||
         fifo_read_err_sum ||
         fifo_status_err_sum)) ||
         // errs not gated by cs_enable
         main_sm_err_sum ||
         fatal_loc_events;

  // set fifo errors that are single instances of source
  assign ctr_drbg_upd_sfifo_final_err_sum = (|ctr_drbg_upd_sfifo_final_err) ||
         err_code_test_bit[9];
  assign ctr_drbg_gen_sfifo_gbencack_err_sum = (|ctr_drbg_gen_sfifo_gbencack_err) ||
         err_code_test_bit[10];
  assign ctr_drbg_gen_sfifo_grcstage_err_sum = (|ctr_drbg_gen_sfifo_grcstage_err) ||
         err_code_test_bit[11];
  assign ctr_drbg_gen_sfifo_gadstage_err_sum = (|ctr_drbg_gen_sfifo_gadstage_err) ||
         err_code_test_bit[13];
  assign ctr_drbg_gen_sfifo_ggenbits_err_sum = (|ctr_drbg_gen_sfifo_ggenbits_err) ||
         err_code_test_bit[14];
  assign block_encrypt_sfifo_cmdid_err_sum = (|block_encrypt_sfifo_cmdid_err) ||
         err_code_test_bit[15];
  assign cmd_stage_sm_err_sum     = (|cmd_stage_sm_err)  || err_code_test_bit[20];
  assign main_sm_err_sum          = cs_main_sm_err       || err_code_test_bit[21];
  assign drbg_gen_sm_err_sum      = drbg_gen_sm_err      || err_code_test_bit[22];
  assign drbg_updbe_sm_err_sum    = drbg_updbe_sm_err    || err_code_test_bit[23];
  assign drbg_updob_sm_err_sum    = drbg_updob_sm_err    || err_code_test_bit[24];
  assign block_encrypt_sm_err_sum = block_encrypt_sm_err || err_code_test_bit[25];
  assign drbg_cmd_sm_err_sum      = drbg_cmd_sm_err      || err_code_test_bit[27];
  assign cmd_gen_cnt_err_sum = (|cmd_gen_cnt_err) || ctr_drbg_gen_v_ctr_err ||
         ctr_drbg_upd_v_ctr_err || err_code_test_bit[26];
  assign fifo_write_err_sum =
         block_encrypt_sfifo_cmdid_err[2] ||
         ctr_drbg_gen_sfifo_ggenbits_err[2] ||
         ctr_drbg_gen_sfifo_gadstage_err[2] ||
         ctr_drbg_gen_sfifo_grcstage_err[2] ||
         ctr_drbg_gen_sfifo_gbencack_err[2] ||
         ctr_drbg_upd_sfifo_final_err[2] ||
         (|cmd_stage_sfifo_genbits_err_wr) ||
         (|cmd_stage_sfifo_cmd_err_wr) ||
         err_code_test_bit[28];
  assign fifo_read_err_sum =
         block_encrypt_sfifo_cmdid_err[1] ||
         ctr_drbg_gen_sfifo_ggenbits_err[1] ||
         ctr_drbg_gen_sfifo_gadstage_err[1] ||
         ctr_drbg_gen_sfifo_grcstage_err[1] ||
         ctr_drbg_gen_sfifo_gbencack_err[1] ||
         ctr_drbg_upd_sfifo_final_err[1] ||
         (|cmd_stage_sfifo_genbits_err_rd) ||
         (|cmd_stage_sfifo_cmd_err_rd) ||
         err_code_test_bit[29];
  assign fifo_status_err_sum =
         block_encrypt_sfifo_cmdid_err[0] ||
         ctr_drbg_gen_sfifo_ggenbits_err[0] ||
         ctr_drbg_gen_sfifo_gadstage_err[0] ||
         ctr_drbg_gen_sfifo_grcstage_err[0] ||
         ctr_drbg_gen_sfifo_gbencack_err[0] ||
         ctr_drbg_upd_sfifo_final_err[0] ||
         (|cmd_stage_sfifo_genbits_err_st) ||
         (|cmd_stage_sfifo_cmd_err_st) ||
         err_code_test_bit[30];

  // set the err code source bits
  assign hw2reg.err_code.sfifo_cmd_err.d = 1'b1;
  assign hw2reg.err_code.sfifo_cmd_err.de = cs_enable_fo[2] &&
         (|cmd_stage_sfifo_cmd_err_sum);

  assign hw2reg.err_code.sfifo_genbits_err.d = 1'b1;
  assign hw2reg.err_code.sfifo_genbits_err.de = cs_enable_fo[3] &&
         (|cmd_stage_sfifo_genbits_err_sum);

  assign hw2reg.err_code.sfifo_final_err.d = 1'b1;
  assign hw2reg.err_code.sfifo_final_err.de = cs_enable_fo[11] &&
         ctr_drbg_upd_sfifo_final_err_sum;

  assign hw2reg.err_code.sfifo_gbencack_err.d = 1'b1;
  assign hw2reg.err_code.sfifo_gbencack_err.de = cs_enable_fo[12] &&
         ctr_drbg_gen_sfifo_gbencack_err_sum;

  assign hw2reg.err_code.sfifo_grcstage_err.d = 1'b1;
  assign hw2reg.err_code.sfifo_grcstage_err.de = cs_enable_fo[13] &&
         ctr_drbg_gen_sfifo_grcstage_err_sum;

  assign hw2reg.err_code.sfifo_gadstage_err.d = 1'b1;
  assign hw2reg.err_code.sfifo_gadstage_err.de = cs_enable_fo[15] &&
         ctr_drbg_gen_sfifo_gadstage_err_sum;

  assign hw2reg.err_code.sfifo_ggenbits_err.d = 1'b1;
  assign hw2reg.err_code.sfifo_ggenbits_err.de = cs_enable_fo[16] &&
         ctr_drbg_gen_sfifo_ggenbits_err_sum;

  assign hw2reg.err_code.sfifo_cmdid_err.d = 1'b1;
  assign hw2reg.err_code.sfifo_cmdid_err.de = cs_enable_fo[17] &&
         block_encrypt_sfifo_cmdid_err_sum;

  assign hw2reg.err_code.cmd_stage_sm_err.d = 1'b1;
  assign hw2reg.err_code.cmd_stage_sm_err.de = cs_enable_fo[18] &&
         cmd_stage_sm_err_sum;

  assign hw2reg.err_code.main_sm_err.d = 1'b1;
  assign hw2reg.err_code.main_sm_err.de = cs_enable_fo[19] &&
         main_sm_err_sum;

  assign hw2reg.err_code.drbg_cmd_sm_err.d = 1'b1;
  assign hw2reg.err_code.drbg_cmd_sm_err.de = cs_enable_fo[10] &&
         drbg_cmd_sm_err_sum;

  assign hw2reg.err_code.drbg_gen_sm_err.d = 1'b1;
  assign hw2reg.err_code.drbg_gen_sm_err.de = cs_enable_fo[20] &&
         drbg_gen_sm_err_sum;

  assign hw2reg.err_code.drbg_updbe_sm_err.d = 1'b1;
  assign hw2reg.err_code.drbg_updbe_sm_err.de = cs_enable_fo[21] &&
         drbg_updbe_sm_err_sum;

  assign hw2reg.err_code.drbg_updob_sm_err.d = 1'b1;
  assign hw2reg.err_code.drbg_updob_sm_err.de = cs_enable_fo[22] &&
         drbg_updob_sm_err_sum;

  assign hw2reg.err_code.aes_cipher_sm_err.d = 1'b1;
  assign hw2reg.err_code.aes_cipher_sm_err.de = cs_enable_fo[23] &&
         block_encrypt_sm_err_sum;

  assign hw2reg.err_code.cmd_gen_cnt_err.d = 1'b1;
  assign hw2reg.err_code.cmd_gen_cnt_err.de = cmd_gen_cnt_err_sum;


 // set the err code type bits
  assign hw2reg.err_code.fifo_write_err.d = 1'b1;
  assign hw2reg.err_code.fifo_write_err.de = cs_enable_fo[24] && fifo_write_err_sum;

  assign hw2reg.err_code.fifo_read_err.d = 1'b1;
  assign hw2reg.err_code.fifo_read_err.de = cs_enable_fo[25] && fifo_read_err_sum;

  assign hw2reg.err_code.fifo_state_err.d = 1'b1;
  assign hw2reg.err_code.fifo_state_err.de = cs_enable_fo[26] && fifo_status_err_sum;

  // Error forcing
  for (genvar i = 0; i < 31; i = i+1) begin : gen_err_code_test_bit
    assign err_code_test_bit[i] = (reg2hw.err_code_test.q == i) && reg2hw.err_code_test.qe;
  end : gen_err_code_test_bit

  // alert - send all interrupt sources to the alert for the fatal case
  assign fatal_alert_o = event_cs_fatal_err;

  // alert test
  assign recov_alert_test_o = {
    reg2hw.alert_test.recov_alert.q &&
    reg2hw.alert_test.recov_alert.qe
  };
  assign fatal_alert_test_o = {
    reg2hw.alert_test.fatal_alert.q &&
    reg2hw.alert_test.fatal_alert.qe
  };


  assign recov_alert_event = cs_enable_pfa ||
         sw_app_enable_pfa ||
         read_int_state_pfa ||
         acmd_flag0_pfa ||
         |reseed_cnt_alert ||
         |invalid_cmd_seq_alert ||
         |invalid_acmd_alert ||
         cs_bus_cmp_alert;


  prim_edge_detector #(
    .Width(1),
    .ResetValue(0),
    .EnSync(0)
  ) u_prim_edge_detector_recov_alert (
    .clk_i,
    .rst_ni,
    .d_i(recov_alert_event),
    .q_sync_o(),
    .q_posedge_pulse_o(recov_alert_o),
    .q_negedge_pulse_o()
  );


  // check for illegal enable field states, and set alert if detected

  // SEC_CM: CONFIG.MUBI
  mubi4_t mubi_cs_enable;
  assign mubi_cs_enable = mubi4_t'(reg2hw.ctrl.enable.q);
  assign cs_enable_pfa = mubi4_test_invalid(mubi_cs_enable_fanout[0]);
  assign hw2reg.recov_alert_sts.enable_field_alert.de = cs_enable_pfa;
  assign hw2reg.recov_alert_sts.enable_field_alert.d  = cs_enable_pfa;

  for (genvar i = 1; i < CsEnableCopies; i = i+1) begin : gen_mubi_en_copies
    assign cs_enable_fo[i] = mubi4_test_true_strict(mubi_cs_enable_fanout[i]);
  end : gen_mubi_en_copies

  prim_mubi4_sync #(
    .NumCopies(CsEnableCopies),
    .AsyncOn(0)
  ) u_prim_mubi4_sync_cs_enable (
    .clk_i,
    .rst_ni,
    .mubi_i(mubi_cs_enable),
    .mubi_o(mubi_cs_enable_fanout)
  );

  // SEC_CM: CONFIG.MUBI
  mubi4_t mubi_sw_app_enable;
  mubi4_t [1:0] mubi_sw_app_enable_fanout;
  assign mubi_sw_app_enable = mubi4_t'(reg2hw.ctrl.sw_app_enable.q);
  assign sw_app_enable_pfe = mubi4_test_true_strict(mubi_sw_app_enable_fanout[0]);
  assign sw_app_enable_pfa = mubi4_test_invalid(mubi_sw_app_enable_fanout[1]);
  assign hw2reg.recov_alert_sts.sw_app_enable_field_alert.de = sw_app_enable_pfa;
  assign hw2reg.recov_alert_sts.sw_app_enable_field_alert.d  = sw_app_enable_pfa;

  prim_mubi4_sync #(
    .NumCopies(2),
    .AsyncOn(0)
  ) u_prim_mubi4_sync_sw_app_enable (
    .clk_i,
    .rst_ni,
    .mubi_i(mubi_sw_app_enable),
    .mubi_o(mubi_sw_app_enable_fanout)
  );

  // SEC_CM: CONFIG.MUBI
  mubi4_t mubi_read_int_state;
  mubi4_t [1:0] mubi_read_int_state_fanout;
  assign mubi_read_int_state = mubi4_t'(reg2hw.ctrl.read_int_state.q);
  assign read_int_state_pfe = mubi4_test_true_strict(mubi_read_int_state_fanout[0]);
  assign read_int_state_pfa = mubi4_test_invalid(mubi_read_int_state_fanout[1]);
  assign hw2reg.recov_alert_sts.read_int_state_field_alert.de = read_int_state_pfa;
  assign hw2reg.recov_alert_sts.read_int_state_field_alert.d  = read_int_state_pfa;

  prim_mubi4_sync #(
    .NumCopies(2),
    .AsyncOn(0)
  ) u_prim_mubi4_sync_read_int_state (
    .clk_i,
    .rst_ni,
    .mubi_i(mubi_read_int_state),
    .mubi_o(mubi_read_int_state_fanout)
  );

  // SEC_CM: CONFIG.MUBI
  mubi4_t mubi_fips_force_enable;
  mubi4_t [1:0] mubi_fips_force_enable_fanout;
  assign mubi_fips_force_enable = mubi4_t'(reg2hw.ctrl.fips_force_enable.q);
  assign fips_force_enable_pfe = mubi4_test_true_strict(mubi_fips_force_enable_fanout[0]);
  assign fips_force_enable_pfa = mubi4_test_invalid(mubi_fips_force_enable_fanout[1]);
  assign hw2reg.recov_alert_sts.fips_force_enable_field_alert.de = fips_force_enable_pfa;
  assign hw2reg.recov_alert_sts.fips_force_enable_field_alert.d  = fips_force_enable_pfa;

  prim_mubi4_sync #(
    .NumCopies(2),
    .AsyncOn(0)
  ) u_prim_mubi4_sync_fips_force_enable (
    .clk_i,
    .rst_ni,
    .mubi_i(mubi_fips_force_enable),
    .mubi_o(mubi_fips_force_enable_fanout)
  );

  // master module enable
  assign sw_app_enable = sw_app_enable_pfe;
  assign read_int_state = read_int_state_pfe;
  assign fips_force_enable = fips_force_enable_pfe;

  //------------------------------------------
  // application interface
  //------------------------------------------
  // Each application port has its own
  // csrng_cmd_stage block to receive the
  // command, track the state of its completion,
  // and return any genbits if the command
  // is a generate command.

  for (genvar ai = 0; ai < NumApps; ai = ai+1) begin : gen_cmd_stage

    csrng_cmd_stage u_csrng_cmd_stage (
      .clk_i                        (clk_i),
      .rst_ni                       (rst_ni),
      .cs_enable_i                  (cs_enable_fo[27]),
      .cmd_stage_vld_i              (cmd_stage_vld[ai]),
      .cmd_stage_shid_i             (cmd_stage_shid[ai]),
      .cmd_stage_bus_i              (cmd_stage_bus[ai]),
      .cmd_stage_rdy_o              (cmd_stage_rdy[ai]),
      .reseed_cnt_reached_i         (reseed_cnt_reached_q[ai]),
      .reseed_cnt_alert_o           (reseed_cnt_alert[ai]),
      .invalid_cmd_seq_alert_o      (invalid_cmd_seq_alert[ai]),
      .invalid_acmd_alert_o         (invalid_acmd_alert[ai]),
      .cmd_arb_req_o                (cmd_arb_req[ai]),
      .cmd_arb_sop_o                (cmd_arb_sop[ai]),
      .cmd_arb_mop_o                (cmd_arb_mop[ai]),
      .cmd_arb_eop_o                (cmd_arb_eop[ai]),
      .cmd_arb_gnt_i                (cmd_arb_gnt[ai]),
      .cmd_arb_bus_o                (cmd_arb_bus[ai]),
      .cmd_ack_i                    (cmd_core_ack[ai]),
      .cmd_ack_sts_i                (cmd_core_ack_sts[ai]),
      .cmd_stage_ack_o              (cmd_stage_ack[ai]),
      .cmd_stage_ack_sts_o          (cmd_stage_ack_sts[ai]),
      .genbits_vld_i                (genbits_core_vld[ai]),
      .genbits_bus_i                (genbits_core_bus[ai]),
      .genbits_fips_i               (genbits_core_fips[ai]),
      .genbits_vld_o                (genbits_stage_vld[ai]),
      .genbits_rdy_i                (genbits_stage_rdy[ai]),
      .genbits_bus_o                (genbits_stage_bus[ai]),
      .genbits_fips_o               (genbits_stage_fips[ai]),
      .cmd_stage_sfifo_cmd_err_o    (cmd_stage_sfifo_cmd_err[ai]),
      .cmd_stage_sfifo_genbits_err_o(cmd_stage_sfifo_genbits_err[ai]),
      .cmd_gen_cnt_err_o            (cmd_gen_cnt_err[ai]),
      .cmd_stage_sm_err_o           (cmd_stage_sm_err[ai])
    );

    // Set reseed_cnt_reached_d to true if the max number of generate requests between reseeds
    // has been reached for the respective counter.
    assign reseed_cnt_reached_d[ai] = (state_db_wr_vld && (state_db_wr_data.inst_id == ai)) ?
                                      (state_db_wr_data.rs_ctr >= reg2hw.reseed_interval.q) :
                                      reseed_cnt_reached_q[ai];

  end : gen_cmd_stage

  // SW interface connection (only 1, and must be present)
  // cmd req
  assign cmd_stage_vld[NumApps-1] = reg2hw.cmd_req.qe;
  assign cmd_stage_shid[NumApps-1] = InstIdWidth'(NumApps-1);
  assign cmd_stage_bus[NumApps-1] = reg2hw.cmd_req.q;
  assign hw2reg.sw_cmd_sts.cmd_rdy.de = 1'b1;
  assign hw2reg.sw_cmd_sts.cmd_rdy.d = cmd_rdy;
  assign cmd_rdy = !cmd_stage_vld[NumApps-1] && sw_rdy_sts_q;
  assign sw_rdy_sts_d =
         !cs_enable_fo[28] ? 1'b0 :
         cmd_stage_vld[NumApps-1] ? 1'b0 :
         cmd_stage_rdy[NumApps-1] ? 1'b1 :
         sw_rdy_sts_q;
  // cmd sts ack
  assign hw2reg.sw_cmd_sts.cmd_ack.de = 1'b1;
  assign hw2reg.sw_cmd_sts.cmd_ack.d = sw_sts_ack_d;
  assign sw_sts_ack = cmd_stage_ack[NumApps-1];
  assign sw_sts_ack_d =
         !cs_enable_fo[28] ? 1'b0 :
         cmd_stage_vld[NumApps-1] ? 1'b0 :
         cmd_stage_ack[NumApps-1] ? 1'b1 :
         sw_sts_ack_q;
  // cmd ack sts
  assign hw2reg.sw_cmd_sts.cmd_sts.de = cmd_stage_ack[NumApps-1];
  assign hw2reg.sw_cmd_sts.cmd_sts.d = cmd_stage_ack_sts[NumApps-1];
  // genbits
  assign hw2reg.genbits_vld.genbits_vld.d = genbits_stage_vldo_sw;
  assign hw2reg.genbits_vld.genbits_fips.d = genbits_stage_fips_sw;
  assign hw2reg.genbits.d = (sw_app_enable && otp_sw_app_read_en[0]) ? genbits_stage_bus_sw : '0;
  assign genbits_stage_bus_rd_sw = reg2hw.genbits.re;

  assign otp_sw_app_read_en[0] = prim_mubi_pkg::mubi8_test_true_strict(otp_sw_app_read_en_mubi[0]);
  assign otp_sw_app_read_en[1] = prim_mubi_pkg::mubi8_test_true_strict(otp_sw_app_read_en_mubi[1]);

  prim_mubi8_sync #(
    .NumCopies(2),
    .AsyncOn(1)
  ) u_prim_mubi8_sync_sw_app_read (
    .clk_i,
    .rst_ni,
    .mubi_i(otp_en_csrng_sw_app_read_i),
    .mubi_o(otp_sw_app_read_en_mubi)
  );

  // pack the gen bits into a 32 bit register sized word
  prim_packer_fifo #(
    .InW(BlkLen),
    .OutW(32),
    .ClearOnRead(1'b0)
  ) u_prim_packer_fifo_sw_genbits (
    .clk_i   (clk_i),
    .rst_ni  (rst_ni),
    .clr_i   (!cs_enable_fo[29]),
    .wvalid_i(genbits_stage_vld[NumApps-1]),
    .wdata_i (genbits_stage_bus[NumApps-1]),
    .wready_o(genbits_stage_rdy[NumApps-1]),
    .rvalid_o(genbits_stage_vldo_sw),
    .rdata_o (genbits_stage_bus_sw),
    .rready_i(genbits_stage_bus_rd_sw),
    .depth_o ()
  );

  // flops for SW fips status
  assign genbits_stage_fips_sw_d =
         (!cs_enable_fo[30]) ? 1'b0 :
         (genbits_stage_rdy[NumApps-1] && genbits_stage_vld[NumApps-1]) ?
                                          genbits_stage_fips[NumApps-1] :
                                          genbits_stage_fips_sw_q;

  assign genbits_stage_fips_sw = genbits_stage_fips_sw_q;


  //--------------------------------------------
  // data path integrity check
  // - a countermeasure to detect entropy bus tampering attempts
  // - checks to make sure repeated data sets off an alert for sw to handle
  //--------------------------------------------

  // SEC_CM: SW_GENBITS.BUS.CONSISTENCY

  // capture a copy of the genbits data
  assign cs_rdata_capt_vld = (genbits_stage_vld[NumApps-1] && genbits_stage_rdy[NumApps-1]);

  assign cs_rdata_capt_d = cs_rdata_capt_vld ? genbits_stage_bus[NumApps-1][63:0] : cs_rdata_capt_q;

  assign cs_rdata_capt_vld_d =
         !cs_enable_fo[31] ? 1'b0 :
         cs_rdata_capt_vld ? 1'b1 :
         cs_rdata_capt_vld_q;

  // continuous compare of the entropy data for sw port
  assign cs_bus_cmp_alert = cs_rdata_capt_vld && cs_rdata_capt_vld_q &&
         (cs_rdata_capt_q == genbits_stage_bus[NumApps-1][63:0]); // only look at 64 bits

  assign hw2reg.recov_alert_sts.cs_bus_cmp_alert.de = cs_bus_cmp_alert;
  assign hw2reg.recov_alert_sts.cs_bus_cmp_alert.d  = cs_bus_cmp_alert;

  assign hw2reg.recov_alert_sts.cmd_stage_invalid_acmd_alert.de = |invalid_acmd_alert;
  assign hw2reg.recov_alert_sts.cmd_stage_invalid_acmd_alert.d  = |invalid_acmd_alert;

  assign hw2reg.recov_alert_sts.cmd_stage_invalid_cmd_seq_alert.de = |invalid_cmd_seq_alert;
  assign hw2reg.recov_alert_sts.cmd_stage_invalid_cmd_seq_alert.d  = |invalid_cmd_seq_alert;

  assign hw2reg.recov_alert_sts.cmd_stage_reseed_cnt_alert.de = |reseed_cnt_alert;
  assign hw2reg.recov_alert_sts.cmd_stage_reseed_cnt_alert.d  = |reseed_cnt_alert;

  // HW interface connections (up to 16, numbered 0-14)
  for (genvar hai = 0; hai < (NumApps-1); hai = hai+1) begin : gen_app_if
    // cmd req
    assign cmd_stage_vld[hai] = csrng_cmd_i[hai].csrng_req_valid;
    assign cmd_stage_shid[hai] = hai;
    assign cmd_stage_bus[hai] = csrng_cmd_i[hai].csrng_req_bus;
    assign csrng_cmd_o[hai].csrng_req_ready = cmd_stage_rdy[hai];
    // cmd ack
    assign csrng_cmd_o[hai].csrng_rsp_ack = cmd_stage_ack[hai];
    assign csrng_cmd_o[hai].csrng_rsp_sts = cmd_stage_ack_sts[hai];
    // genbits
    assign csrng_cmd_o[hai].genbits_valid = genbits_stage_vld[hai];
    assign csrng_cmd_o[hai].genbits_fips = genbits_stage_fips[hai];
    assign csrng_cmd_o[hai].genbits_bus = genbits_stage_bus[hai];
    assign genbits_stage_rdy[hai] = csrng_cmd_i[hai].genbits_ready;
  end : gen_app_if

  // set ack status for configured instances
  for (genvar i = 0; i < NumHwApps; i = i+1) begin : gen_app_if_sts
    assign hw_exception_sts[i] = cmd_stage_ack[i] && (cmd_stage_ack_sts[i] != CMD_STS_SUCCESS);
  end : gen_app_if_sts

  // set ack status to zero for un-configured instances
  for (genvar i = NumHwApps; i < 16; i = i+1) begin : gen_app_if_zero_sts
    assign hw_exception_sts[i] = 1'b0;
  end : gen_app_if_zero_sts

  // set fifo err status bits
  for (genvar i = 0; i < NumApps; i = i+1) begin : gen_fifo_sts
    assign cmd_stage_sfifo_cmd_err_sum[i] = (|cmd_stage_sfifo_cmd_err[i] ||
                                             err_code_test_bit[0]);
    assign cmd_stage_sfifo_cmd_err_wr[i] = cmd_stage_sfifo_cmd_err[i][2];
    assign cmd_stage_sfifo_cmd_err_rd[i] = cmd_stage_sfifo_cmd_err[i][1];
    assign cmd_stage_sfifo_cmd_err_st[i] = cmd_stage_sfifo_cmd_err[i][0];
    assign cmd_stage_sfifo_genbits_err_sum[i] = (|cmd_stage_sfifo_genbits_err[i] ||
                                                 err_code_test_bit[1]);
    assign cmd_stage_sfifo_genbits_err_wr[i] = cmd_stage_sfifo_genbits_err[i][2];
    assign cmd_stage_sfifo_genbits_err_rd[i] = cmd_stage_sfifo_genbits_err[i][1];
    assign cmd_stage_sfifo_genbits_err_st[i] = cmd_stage_sfifo_genbits_err[i][0];
  end : gen_fifo_sts

  //------------------------------------------
  // app command arbiter and state machine
  //------------------------------------------
  // All commands that arrive from the
  // application ports are arbitrated for
  // and processed by the main state machine
  // logic block.

  assign cmd_arb_idx_d = (acmd_avail && acmd_accept) ? cmd_arb_idx : cmd_arb_idx_q;

  assign acmd_sop = cmd_arb_sop[cmd_arb_idx_q];
  assign acmd_mop = cmd_arb_mop[cmd_arb_idx_q];
  assign acmd_eop = cmd_arb_eop[cmd_arb_idx_q];
  assign acmd_bus = cmd_arb_bus[cmd_arb_idx_q];

  prim_arbiter_ppc #(
    .EnDataPort(0),    // Ignore data port
    .N(NumApps),  // Number of request ports
    .DW(1) // Data width
  ) u_prim_arbiter_ppc_acmd (
    .clk_i    (clk_i),
    .rst_ni   (rst_ni),
    .req_chk_i(cs_enable_fo[1]),
    .req_i    (cmd_arb_req),
    .data_i   ('{default: 1'b0}),
    .gnt_o    (cmd_arb_gnt),
    .idx_o    (cmd_arb_idx),
    .valid_o  (acmd_avail), // 1 req
    .data_o   (), //NC
    .ready_i  (acmd_accept) // 1 fsm rdy
  );

  assign acmd_flag0_pfa = mubi4_test_invalid(flag0_q);
  assign hw2reg.recov_alert_sts.acmd_flag0_field_alert.de = acmd_flag0_pfa;
  assign hw2reg.recov_alert_sts.acmd_flag0_field_alert.d  = acmd_flag0_pfa;

  // parse the command bus
  assign acmd_hold = acmd_sop ? acmd_e'(acmd_bus[CmdWidth-1:0]) : acmd_q;

  // TODO(#28153) rewrite as an always_comb block
  assign acmd_d =
         (!cs_enable_fo[32]) ? INV :
         acmd_sop ? acmd_e'(acmd_bus[CmdWidth-1:0]) :
         acmd_q;

  assign shid_d =
         (!cs_enable_fo[33]) ? '0 :
         acmd_sop ? acmd_bus[15:12] :
         shid_q;

  assign gen_last_d =
         (!cs_enable_fo[34]) ? '0 :
         acmd_sop ? acmd_bus[16] :
         gen_last_q;

  assign flag0_d =
         (!cs_enable_fo[35]) ? prim_mubi_pkg::MuBi4False :
         (acmd_sop && ((acmd_bus[2:0] == INS) || (acmd_bus[2:0] == RES))) ?
          mubi4_t'(acmd_bus[11:8]) : flag0_q;

  // SEC_CM: CTRL.MUBI
  mubi4_t mubi_flag0;
  assign mubi_flag0 = flag0_q;

  for (genvar i = 0; i < Flag0Copies; i = i+1) begin : gen_mubi_flag0_copies
    assign flag0_fo[i] = mubi4_test_true_strict(mubi_flag0_fanout[i]);
  end : gen_mubi_flag0_copies

  prim_mubi4_sync #(
    .NumCopies(Flag0Copies),
    .AsyncOn(0)
  ) u_prim_mubi4_sync_flag0 (
    .clk_i,
    .rst_ni,
    .mubi_i(mubi_flag0),
    .mubi_o(mubi_flag0_fanout)
  );

  // sm to process all instantiation requests
  // SEC_CM: MAIN_SM.CTR.LOCAL_ESC
  // SEC_CM: MAIN_SM.FSM.SPARSE
  csrng_main_sm u_csrng_main_sm (
    .clk_i                 (clk_i),
    .rst_ni                (rst_ni),
    .enable_i              (cs_enable_fo[36]),
    .acmd_avail_i          (acmd_avail),
    .acmd_accept_o         (acmd_accept),
    .acmd_i                (acmd_hold),
    .acmd_eop_i            (acmd_eop),
    .flag0_i               (flag0_fo[0]),
    .cmd_entropy_req_o     (cmd_entropy_req),
    .cmd_entropy_avail_i   (cmd_entropy_avail),
    .cmd_vld_o             (main_sm_cmd_vld),
    .cmd_rdy_i             (ctr_drbg_cmd_req_rdy),
    .clr_adata_packer_o    (clr_adata_packer),
    .cmd_complete_i        (state_db_wr_vld),
    .local_escalate_i      (fatal_loc_events),
    .main_sm_state_o       (cs_main_sm_state),
    .main_sm_err_o         (cs_main_sm_err)
  );

  // interrupt for sw app interface only
  assign event_cs_cmd_req_done = sw_sts_ack;

  // interrupt for entropy request
  assign event_cs_entropy_req = entropy_src_hw_if_o.es_req;

  // interrupt for app interface exception
  assign event_cs_hw_inst_exc = |hw_exception_sts;

  // entropy available
  assign cmd_entropy_avail = entropy_src_hw_if_i.es_ack;

  for (genvar csi = 0; csi < NumApps; csi = csi+1) begin : gen_cmd_ack
    assign cmd_core_ack[csi] = state_db_sts_ack && (state_db_sts_id == csi);
    assign cmd_core_ack_sts[csi] = state_db_sts_sts;
    assign genbits_core_vld[csi] = ctr_drbg_gen_rsp_vld && (ctr_drbg_gen_rsp_data.inst_id == csi);
    assign genbits_core_bus[csi] = ctr_drbg_gen_rsp_bits;
    assign genbits_core_fips[csi] = ctr_drbg_gen_rsp_data.fips;
  end : gen_cmd_ack


  prim_packer_fifo #(
    .InW(32),
    .OutW(SeedLen),
    .ClearOnRead(1'b1)
  ) u_prim_packer_fifo_adata (
    .clk_i   (clk_i),
    .rst_ni  (rst_ni),
    .clr_i   (!cs_enable_fo[37] || packer_adata_clr),
    .wvalid_i(acmd_mop),
    .wdata_i (acmd_bus),
    .wready_o(),
    .rvalid_o(),
    .rdata_o (packer_adata),
    .rready_i(packer_adata_pop),
    .depth_o (packer_adata_depth)
  );

  assign packer_adata_pop = cs_enable_fo[38] &&
         clr_adata_packer && (packer_adata_depth == ADataDepthClog'(CmdMaxClen));

  assign packer_adata_clr = cs_enable_fo[39] &&
         clr_adata_packer && (packer_adata_depth < ADataDepthClog'(CmdMaxClen));

  //-------------------------------------
  // csrng_state_db instantiation
  //-------------------------------------
  // This block holds the internal state
  // of each csrng instance. The state
  // is updated after each command.

  assign state_db_reg_read_en = cs_enable_fo[40] && read_int_state && otp_sw_app_read_en[1];

  csrng_state_db u_csrng_state_db (
    .clk_i   (clk_i),
    .rst_ni  (rst_ni),
    .enable_i(cs_enable_fo[41]),

    .rd_inst_id_i(shid_q),
    .rd_state_o  (state_db_rd_data),

    .wr_vld_i   (state_db_wr_vld),
    .wr_data_i  (state_db_wr_data),
    .wr_status_i(state_db_wr_sts),

    .reg_rd_otp_en_i    (state_db_reg_read_en),
    .reg_rd_regfile_en_i(reg2hw.int_state_read_enable.q),

    .reg_rd_id_vld_i(reg2hw.int_state_num.qe),
    .reg_rd_id_i    (reg2hw.int_state_num.q),
    .reg_rd_strb_i  (reg2hw.int_state_val.re),
    .reg_rd_val_o   (hw2reg.int_state_val.d),

    .status_vld_o    (state_db_sts_ack),
    .status_val_o    (state_db_sts_sts),
    .status_inst_id_o(state_db_sts_id),

    .reseed_counter_o(reseed_counter)
  );

  logic cmd_rsp_to_state_db;

  // Keep forwarding gen unit responses to the state db unless the cmd unit has a valid response.
  assign cmd_rsp_to_state_db = (ctr_drbg_cmd_rsp_data.cmd != GEN) && (ctr_drbg_cmd_rsp_vld == 1'b1);

  assign state_db_wr_vld  = cmd_rsp_to_state_db ?  ctr_drbg_cmd_rsp_vld : ctr_drbg_gen_rsp_vld;
  assign state_db_wr_data = cmd_rsp_to_state_db ? ctr_drbg_cmd_rsp_data : ctr_drbg_gen_rsp_data;
  assign state_db_wr_sts  = cmd_rsp_to_state_db ?       CMD_STS_SUCCESS : ctr_drbg_gen_rsp_sts;

  // Tie gen unit request to zero if cmd unit writes to state db
  assign ctr_drbg_gen_req_vld = cmd_rsp_to_state_db ? 1'b0 : ctr_drbg_cmd_rsp_vld;
  // State db is always ready to write; the respective response ready signal can be tied high
  assign ctr_drbg_gen_rsp_rdy = cmd_rsp_to_state_db ? 1'b0 : 1'b1;
  // Response ready for cmd unit cannot depend on its response valid to avoid combinational loop,
  // hence cmd_rsp_to_state_db cannot be used here.
  assign ctr_drbg_cmd_rsp_rdy = (ctr_drbg_cmd_rsp_data.cmd == GEN) ? ctr_drbg_gen_req_rdy : 1'b1;

  // Forward the reseed counter values to the register interface.
  always_comb begin : reseed_counter_assign
    for (int i = 0; i < NumApps; i++) begin
      hw2reg.reseed_counter[i].d = reseed_counter[i];
    end
  end

  //--------------------------------------------
  // entropy interface
  //--------------------------------------------
  // Basic interface logic with the entropy_src block

  assign entropy_src_hw_if_o.es_req = cs_enable_fo[43] && cmd_entropy_req;


  // SEC_CM: CONSTANTS.LC_GATED
  assign seed_diversification = lc_hw_debug_on_fo[0] ? RndCnstCsKeymgrDivNonProduction :
                                                       RndCnstCsKeymgrDivProduction;

  // Capture entropy from entropy_src
  assign entropy_src_seed_d =
         flag0_fo[1] ? '0 : // special case where zero is used
         cmd_entropy_req && cmd_entropy_avail ?
            (entropy_src_hw_if_i.es_bits ^ seed_diversification) :
         entropy_src_seed_q;
  assign entropy_src_fips_d =
         // Use shid_d here such that u_csrng_ctr_drbg_cmd gets the shid_q and the proper
         // entropy_src_fips_q in the next clock cycle.
         fips_force_enable && reg2hw.fips_force.q[shid_d[NumAppsLg-1:0]] ? 1'b1 :
         flag0_fo[2] ? '0 : // special case where zero is used
         cmd_entropy_req && cmd_entropy_avail ? entropy_src_hw_if_i.es_fips :
         entropy_src_fips_q;

  assign cmd_entropy      = entropy_src_seed_q;
  assign cmd_entropy_fips = entropy_src_fips_q;

  //-------------------------------------
  // csrng_ctr_drbg_cmd instantiation
  //-------------------------------------
  // commands and input parameters
  // ins -> send to csrng_state_db
  //  inputs:  384b entropy, 384b adata
  //  outputs: 416b K,V,RC
  //
  // res -> send to csrng_state_db
  //  inputs:  416b K,V,RC, 384b entropy, 384b adata
  //  outputs: 416b K,V,RC
  //
  // gen -> send to csrng_ctr_drbg_gen block
  //  inputs:  416b K,V,RC, 384b adata
  //  outputs: 416b K,V,RC, 384b adata
  //
  // gen blk -> send to csrng_state_db
  //  inputs:  416b K,V,RC, 384b adata
  //  outputs: 416b K,V,RC, 128b genbits
  //
  // upd -> send to csrng_state_db
  //  inputs:  416b K,V,RC, 384b adata
  //  outputs: 416b K,V,RC

  assign ctr_drbg_cmd_req_vld = !cs_enable_fo[45] ? 1'b0 : main_sm_cmd_vld;
  assign cmd_req_ccmd_dly_d   = !cs_enable_fo[44] ?  INV : acmd_hold;

  assign ctr_drbg_cmd_req_data = '{
    inst_id: shid_q,
    cmd:     cmd_req_ccmd_dly_q,
    key:     state_db_rd_data.key,
    v:       state_db_rd_data.v,
    pdata:   packer_adata,
    rs_ctr:  state_db_rd_data.rs_ctr,
    fips:    state_db_rd_data.fips
  };

  csrng_ctr_drbg_cmd u_csrng_ctr_drbg_cmd (
    .clk_i   (clk_i),
    .rst_ni  (rst_ni),
    .enable_i(cs_enable_fo[46]),

    .req_vld_i         (ctr_drbg_cmd_req_vld),
    .req_rdy_o         (ctr_drbg_cmd_req_rdy),
    .req_data_i        (ctr_drbg_cmd_req_data),
    .req_entropy_i     (cmd_entropy),
    .req_entropy_fips_i(cmd_entropy_fips),
    .req_glast_i       (gen_last_q),

    .rsp_vld_o  (ctr_drbg_cmd_rsp_vld),
    .rsp_rdy_i  (ctr_drbg_cmd_rsp_rdy),
    .rsp_data_o (ctr_drbg_cmd_rsp_data),
    .rsp_glast_o(ctr_drbg_cmd_rsp_glast),

    // Request and response path to and from update unit
    .update_req_vld_o (cmd_upd_req_vld),
    .update_req_rdy_i (cmd_upd_req_rdy),
    .update_req_data_o(cmd_upd_req_data),

    .update_rsp_vld_i (cmd_upd_rsp_vld),
    .update_rsp_rdy_o (cmd_upd_rsp_rdy),
    .update_rsp_data_i(upd_rsp_data),

    .sm_err_o          (drbg_cmd_sm_err)
  );

  //-------------------------------------
  // csrng_ctr_drbg_upd instantiation
  //-------------------------------------
  // The csrng_ctr_drbg_upd is shared
  // between the csrng_ctr_drbg_cmd block
  // and the csrng_ctr_drbg_gen block.
  // The arbiter in this section will
  // route requests and responses between
  // these two blocks.

  csrng_ctr_drbg_upd u_csrng_ctr_drbg_upd (
    .clk_i   (clk_i),
    .rst_ni  (rst_ni),
    .enable_i(cs_enable_fo[47]),

    .req_vld_i (upd_arb_req_vld),
    .req_rdy_o (upd_arb_req_rdy),
    .req_data_i(upd_arb_req_data),

    .rsp_vld_o (upd_rsp_vld),
    .rsp_rdy_i (upd_rsp_rdy),
    .rsp_data_o(upd_rsp_data),

    .es_halt_req_i(cs_aes_halt_i.cs_aes_halt_req),
    .es_halt_ack_o(ctr_drbg_upd_es_ack),

    .block_encrypt_req_vld_o (upd_benc_req_vld),
    .block_encrypt_req_rdy_i (upd_benc_req_rdy),
    .block_encrypt_req_data_o(upd_benc_req_data),

    .block_encrypt_rsp_vld_i (upd_benc_rsp_vld),
    .block_encrypt_rsp_rdy_o (upd_benc_rsp_rdy),
    .block_encrypt_rsp_data_i(block_encrypt_rsp_data),

    .ctr_err_o             (ctr_drbg_upd_v_ctr_err),
    .fifo_final_err_o      (ctr_drbg_upd_sfifo_final_err),
    .sm_block_enc_req_err_o(drbg_updbe_sm_err),
    .sm_block_enc_rsp_err_o(drbg_updob_sm_err)
  );

  // update unit arbiter

  // local helper signals
  csrng_upd_data_t upd_arb_din[2];

  logic [1:0] upd_arb_gnt;

  prim_arbiter_ppc #(
    .N(2), // (cmd req and gen req)
    .DW(UpdDataWidth)
  ) u_prim_arbiter_ppc_updblk_arb (
    .clk_i    (clk_i),
    .rst_ni   (rst_ni),
    .req_chk_i(cs_enable_fo[1]),
    .req_i    ({gen_upd_req_vld, cmd_upd_req_vld}),
    .data_i   (upd_arb_din),
    .gnt_o    (upd_arb_gnt),
    .idx_o    (),
    .valid_o  (upd_arb_req_vld),
    .data_o   (upd_arb_req_data),
    .ready_i  (upd_arb_req_rdy)
  );

  assign upd_arb_din[0] = cmd_upd_req_data;
  assign upd_arb_din[1] = gen_upd_req_data;

  assign cmd_upd_req_rdy = upd_arb_gnt[0];
  assign gen_upd_req_rdy = upd_arb_gnt[1];

  assign cmd_upd_rsp_vld = upd_rsp_vld && (upd_rsp_data.cmd != GENU);
  assign gen_upd_rsp_vld = upd_rsp_vld && (upd_rsp_data.cmd == GENU);

  assign upd_rsp_rdy = (upd_rsp_data.cmd == GENU) ? gen_upd_rsp_rdy : cmd_upd_rsp_rdy;


  //-------------------------------------
  // life cycle logic
  //-------------------------------------
  // The chip level life cycle control
  // provide control logic to determine
  // how certain debug features are controlled.

  lc_ctrl_pkg::lc_tx_t [LcHwDebugCopies-1:0] lc_hw_debug_en_out;

  prim_lc_sync #(
    .NumCopies(LcHwDebugCopies)
  ) u_prim_lc_sync (
    .clk_i,
    .rst_ni,
    .lc_en_i(lc_hw_debug_en_i),
    .lc_en_o({lc_hw_debug_en_out})
  );

  for (genvar i = 0; i < LcHwDebugCopies; i = i+1) begin : gen_lc_dbg_copies
    assign lc_hw_debug_on_fo[i] = lc_ctrl_pkg::lc_tx_test_true_strict(lc_hw_debug_en_out[i]);
  end : gen_lc_dbg_copies


  //-------------------------------------
  // csrng_block_encrypt instantiation
  //-------------------------------------
  // The csrng_block_encrypt is shared
  // between the csrng_ctr_drbg_cmd block
  // and the csrng_ctr_drbg_gen block.
  // The arbiter in this section will
  // route requests and responses between
  // these two blocks.

  csrng_block_encrypt #(
    .SBoxImpl(SBoxImpl)
  ) u_csrng_block_encrypt (
    .clk_i   (clk_i),
    .rst_ni  (rst_ni),
    .enable_i(cs_enable_fo[48]),

    .req_vld_i (block_encrypt_req_vld),
    .req_rdy_o (block_encrypt_req_rdy),
    .req_data_i(block_encrypt_req_data),

    .rsp_vld_o (block_encrypt_rsp_vld),
    .rsp_rdy_i (block_encrypt_rsp_rdy),
    .rsp_data_o(block_encrypt_rsp_data),

    .cipher_quiet_o  (block_encrypt_quiet),
    .cipher_sm_err_o (block_encrypt_sm_err),
    .fifo_cmdid_err_o(block_encrypt_sfifo_cmdid_err)
  );

  // Local helper signals
  csrng_benc_data_t block_encrypt_arb_data[2];

  prim_arbiter_ppc #(
    .N (2), // (upd req and gen req)
    .DW(BencDataWidth)
  ) u_prim_arbiter_ppc_benc_arb (
    .clk_i    (clk_i),
    .rst_ni   (rst_ni),
    .req_chk_i(cs_enable_fo[1]),
    .req_i    ({gen_benc_req_vld, upd_benc_req_vld}),
    .data_i   (block_encrypt_arb_data),
    .gnt_o    ({gen_benc_req_rdy, upd_benc_req_rdy}),
    .idx_o    (),
    .valid_o  (block_encrypt_req_vld),
    .data_o   (block_encrypt_req_data),
    .ready_i  (block_encrypt_req_rdy)
  );

  assign block_encrypt_arb_data[0] = upd_benc_req_data;
  assign block_encrypt_arb_data[1] = gen_benc_req_data;

  // Response valid/ready muxing, depending on the requesting unit
  assign upd_benc_rsp_vld = (block_encrypt_rsp_vld && (block_encrypt_rsp_data.cmd != GENB));
  assign gen_benc_rsp_vld = (block_encrypt_rsp_vld && (block_encrypt_rsp_data.cmd == GENB));

  assign block_encrypt_rsp_rdy = (block_encrypt_rsp_data.cmd == GENB) ? gen_benc_rsp_rdy :
                                                                        upd_benc_rsp_rdy;


  //-------------------------------------
  // csrng_ctr_drbg_gen instantiation
  //-------------------------------------
  // this block performs the second sequence
  // of the generate command. The first part
  // of the sequence is done by the
  // csrng_ctr_drbg_cmd block.

  csrng_ctr_drbg_gen u_csrng_ctr_drbg_gen (
    .clk_i   (clk_i),
    .rst_ni  (rst_ni),
    .enable_i(cs_enable_fo[49]),

    .cmd_req_vld_i  (ctr_drbg_gen_req_vld),
    .cmd_req_rdy_o  (ctr_drbg_gen_req_rdy),
    .cmd_req_data_i (ctr_drbg_cmd_rsp_data),
    .cmd_req_glast_i(ctr_drbg_cmd_rsp_glast),

    .cmd_rsp_vld_o (ctr_drbg_gen_rsp_vld),
    .cmd_rsp_rdy_i (ctr_drbg_gen_rsp_rdy),
    .cmd_rsp_data_o(ctr_drbg_gen_rsp_data),
    .cmd_rsp_bits_o(ctr_drbg_gen_rsp_bits),
    .cmd_rsp_sts_o (ctr_drbg_gen_rsp_sts),

    .es_halt_req_i(cs_aes_halt_i.cs_aes_halt_req),
    .es_halt_ack_o(ctr_drbg_gen_es_ack),

    .update_req_vld_o (gen_upd_req_vld),
    .update_req_rdy_i (gen_upd_req_rdy),
    .update_req_data_o(gen_upd_req_data),

    .update_rsp_vld_i (gen_upd_rsp_vld),
    .update_rsp_rdy_o (gen_upd_rsp_rdy),
    .update_rsp_data_i(upd_rsp_data),

    .block_encrypt_req_vld_o (gen_benc_req_vld),
    .block_encrypt_req_rdy_i (gen_benc_req_rdy),
    .block_encrypt_req_data_o(gen_benc_req_data),

    .block_encrypt_rsp_vld_i (gen_benc_rsp_vld),
    .block_encrypt_rsp_rdy_o (gen_benc_rsp_rdy),
    .block_encrypt_rsp_data_i(block_encrypt_rsp_data),

    .ctr_err_o(ctr_drbg_gen_v_ctr_err),
    .sm_err_o (drbg_gen_sm_err),

    .fifo_gbencack_err_o(ctr_drbg_gen_sfifo_gbencack_err),
    .fifo_grcstage_err_o(ctr_drbg_gen_sfifo_grcstage_err),
    .fifo_gadstage_err_o(ctr_drbg_gen_sfifo_gadstage_err),
    .fifo_ggenbits_err_o(ctr_drbg_gen_sfifo_ggenbits_err)
  );


  // es to cs halt request to reduce power spikes
  assign cs_aes_halt_d =
         (ctr_drbg_upd_es_ack && ctr_drbg_gen_es_ack && block_encrypt_quiet &&
          cs_aes_halt_i.cs_aes_halt_req);

  assign cs_aes_halt_o.cs_aes_halt_ack = cs_aes_halt_q;

  //--------------------------------------------
  // observe state machine
  //--------------------------------------------

  assign hw2reg.main_sm_state.de = 1'b1;
  assign hw2reg.main_sm_state.d = cs_main_sm_state;

  //--------------------------------------------
  // report csrng request summary
  //--------------------------------------------
  // Misc status

  assign hw2reg.hw_exc_sts.de = cs_enable_fo[50];
  assign hw2reg.hw_exc_sts.d  = hw_exception_sts;

  // unused signals
  logic               unused_err_code_test_bit;
  logic               unused_enable_fo;
  logic               unused_reg2hw_genbits;
  logic               unused_int_state_val;
  logic               unused_reseed_interval;
  logic [SeedLen-1:0] unused_gen_rsp_pdata;
  logic               unused_state_db_inst_state;

  assign unused_err_code_test_bit = (|err_code_test_bit[19:16]) || err_code_test_bit[12] ||
                                    (|err_code_test_bit[8:2]);
  assign unused_enable_fo = cs_enable_fo[42] || cs_enable_fo[14] || (|cs_enable_fo[9:4]);
  assign unused_reg2hw_genbits = (|reg2hw.genbits.q);
  assign unused_int_state_val = (|reg2hw.int_state_val.q);
  assign unused_reseed_interval = reg2hw.reseed_interval.qe;
  assign unused_gen_rsp_pdata = ctr_drbg_gen_rsp_data.pdata;
  assign unused_state_db_inst_state = state_db_rd_data.inst_state;

  //--------------------------------------------
  // Assertions
  //--------------------------------------------
`ifdef INC_ASSERT
  // Track activity of AES.
  logic aes_active_d, aes_active_q;
  assign aes_active_d =
      (u_csrng_block_encrypt.u_aes_cipher_core.in_valid_i == aes_pkg::SP2V_HIGH &&
       u_csrng_block_encrypt.u_aes_cipher_core.in_ready_o == aes_pkg::SP2V_HIGH)  ? 1'b1 : // set
      (u_csrng_block_encrypt.u_aes_cipher_core.out_valid_o == aes_pkg::SP2V_HIGH &&
       u_csrng_block_encrypt.u_aes_cipher_core.out_ready_i == aes_pkg::SP2V_HIGH) ? 1'b0 : // clear
      aes_active_q;                                                                        // keep

  // Track state of AES Halt req/ack with entropy_src.
  logic cs_aes_halt_active;
  assign cs_aes_halt_active = cs_aes_halt_i.cs_aes_halt_req & cs_aes_halt_o.cs_aes_halt_ack;

  // Assert that when AES Halt is active, AES is not active.
  `ASSERT(AesNotActiveWhileCsAesHaltActive_A, cs_aes_halt_active |-> !aes_active_d)

  always_ff @(posedge clk_i, negedge rst_ni) begin
    if (!rst_ni) begin
      aes_active_q <= '0;
    end else begin
      aes_active_q <= aes_active_d;
    end
  end

  logic state_db_zeroize;
  assign state_db_zeroize = state_db_wr_vld && (state_db_wr_data.cmd == UNI);
  `ASSERT(CsrngUniZeroizeFips_A, state_db_zeroize -> (state_db_wr_data.fips   == '0))
  `ASSERT(CsrngUniZeroizeKey_A,  state_db_zeroize -> (state_db_wr_data.key    == '0))
  `ASSERT(CsrngUniZeroizeV_A,    state_db_zeroize -> (state_db_wr_data.v      == '0))
  `ASSERT(CsrngUniZeroizeRc_A,   state_db_zeroize -> (state_db_wr_data.rs_ctr == '0))
  `ASSERT(CsrngUniZeroizeSts_A,  state_db_zeroize -> (state_db_wr_sts == '0))

  // Ensure that the ctr_drbg_generate and ctr_drbg_command units never try to write to the
  // state db at the same time.
  `ASSERT(CsrngNoConcurrentGenCmdRsp_A, !(ctr_drbg_cmd_rsp_vld && ctr_drbg_gen_rsp_vld))
`endif

endmodule // csrng_core
