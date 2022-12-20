// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: csrng core module
//


module csrng_core import csrng_pkg::*; #(
  parameter aes_pkg::sbox_impl_e SBoxImpl = aes_pkg::SBoxImplLut,
  parameter int NHwApps = 2,
  parameter cs_keymgr_div_t RndCnstCsKeymgrDivNonProduction = CsKeymgrDivWidth'(0),
  parameter cs_keymgr_div_t RndCnstCsKeymgrDivProduction = CsKeymgrDivWidth'(0)
) (
  input logic                                     clk_i,
  input logic                                     rst_ni,

  input  csrng_reg_pkg::csrng_reg2hw_t            reg2hw,
  output csrng_reg_pkg::csrng_hw2reg_t            hw2reg,

  // Efuse Interface
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
  input  csrng_req_t [NHwApps-1:0]                csrng_cmd_i,
  output csrng_rsp_t [NHwApps-1:0]                csrng_cmd_o,

  // Alerts

  output logic                                    recov_alert_test_o,
  output logic                                    fatal_alert_test_o,
  output logic                                    recov_alert_o,
  output logic                                    fatal_alert_o,

  output logic                                    intr_cs_cmd_req_done_o,
  output logic                                    intr_cs_entropy_req_o,
  output logic                                    intr_cs_hw_inst_exc_o,
  output logic                                    intr_cs_fatal_err_o
);

  import csrng_reg_pkg::*;

  import prim_mubi_pkg::mubi4_t;
  import prim_mubi_pkg::mubi4_test_true_strict;
  import prim_mubi_pkg::mubi4_test_invalid;

  localparam int NApps = NHwApps + 1;
  localparam int AppCmdWidth = 32;
  localparam int AppCmdFifoDepth = 2;
  localparam int GenBitsWidth = 128;
  localparam int Cmd = 3;
  localparam int StateId = 4;
  localparam int KeyLen = 256;
  localparam int BlkLen = 128;
  localparam int SeedLen = 384;
  localparam int CtrLen = 32;
  localparam int NBlkEncArbReqs = 2;
  localparam int BlkEncArbWidth = KeyLen+BlkLen+StateId+Cmd;
  localparam int NUpdateArbReqs = 2;
  localparam int UpdateArbWidth = KeyLen+BlkLen+SeedLen+StateId+Cmd;
  localparam int MaxClen = 12;
  localparam int ADataDepthWidth = SeedLen/AppCmdWidth;
  localparam unsigned ADataDepthClog = $clog2(ADataDepthWidth)+1;
  localparam int CsEnableCopies = 53;
  localparam int LcHwDebugCopies = 1;
  localparam int Flag0Copies = 3;

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
  logic                        recov_alert_event;
  logic                        acmd_avail;
  logic                        acmd_sop;
  logic                        acmd_mop;
  logic                        acmd_eop;

  logic                        cmd_blk_select;
  logic                        gen_blk_select;
  logic                        state_db_wr_req_rdy;
  logic                        state_db_wr_req;
  logic [StateId-1:0]          state_db_wr_inst_id;
  logic [KeyLen-1:0]           state_db_wr_key;
  logic [BlkLen-1:0]           state_db_wr_v;
  logic [CtrLen-1:0]           state_db_wr_rc;
  logic                        state_db_wr_sts;
  logic                        state_db_wr_fips;
  logic [Cmd-1:0]              state_db_wr_ccmd;

  logic [AppCmdWidth-1:0]      acmd_bus;

  logic [SeedLen-1:0]          packer_adata;
  logic [ADataDepthClog-1:0]   packer_adata_depth;
  logic                        packer_adata_pop;
  logic                        packer_adata_clr;
  logic [SeedLen-1:0]          seed_diversification;

  logic                        cmd_entropy_req;
  logic                        cmd_entropy_avail;
  logic                        cmd_entropy_fips;
  logic [SeedLen-1:0]          cmd_entropy;

  logic                        cmd_result_wr_req;
  logic                        cmd_result_ack;
  logic                        cmd_result_ack_sts;
  logic [Cmd-1:0]              cmd_result_ccmd;
  logic                        cmd_result_ack_rdy;
  logic [StateId-1:0]          cmd_result_inst_id;
  logic                        cmd_result_glast;
  logic                        cmd_result_fips;
  logic [SeedLen-1:0]          cmd_result_adata;
  logic [KeyLen-1:0]           cmd_result_key;
  logic [BlkLen-1:0]           cmd_result_v;
  logic [CtrLen-1:0]           cmd_result_rc;

  logic                        state_db_sts_ack;
  logic                        state_db_sts_sts;
  logic [StateId-1:0]          state_db_sts_id;

  logic                        gen_result_wr_req;
  logic                        gen_result_ack_sts;
  logic                        gen_result_ack_rdy;
  logic [Cmd-1:0]              gen_result_ccmd;
  logic [StateId-1:0]          gen_result_inst_id;
  logic                        gen_result_fips;
  logic [KeyLen-1:0]           gen_result_key;
  logic [BlkLen-1:0]           gen_result_v;
  logic [CtrLen-1:0]           gen_result_rc;
  logic [BlkLen-1:0]           gen_result_bits;

  logic                        acmd_accept;
  logic                        instant_req;
  logic                        reseed_req;
  logic                        generate_req;
  logic                        update_req;
  logic                        uninstant_req;
  logic                        clr_adata_packer;
  logic [Cmd-1:0]              ctr_drbg_cmd_ccmd;
  logic                        ctr_drbg_cmd_req;
  logic                        ctr_drbg_gen_req;
  logic                        ctr_drbg_gen_req_rdy;
  logic                        ctr_drbg_cmd_req_rdy;
  logic                        ctr_drbg_cmd_sfifo_cmdreq_err_sum;
  logic [2:0]                  ctr_drbg_cmd_sfifo_cmdreq_err;
  logic                        ctr_drbg_cmd_sfifo_rcstage_err_sum;
  logic [2:0]                  ctr_drbg_cmd_sfifo_rcstage_err;
  logic                        ctr_drbg_cmd_sfifo_keyvrc_err_sum;
  logic [2:0]                  ctr_drbg_cmd_sfifo_keyvrc_err;
  logic                        ctr_drbg_upd_sfifo_updreq_err_sum;
  logic [2:0]                  ctr_drbg_upd_sfifo_updreq_err;
  logic                        ctr_drbg_upd_sfifo_bencreq_err_sum;
  logic [2:0]                  ctr_drbg_upd_sfifo_bencreq_err;
  logic                        ctr_drbg_upd_sfifo_bencack_err_sum;
  logic [2:0]                  ctr_drbg_upd_sfifo_bencack_err;
  logic                        ctr_drbg_upd_sfifo_pdata_err_sum;
  logic [2:0]                  ctr_drbg_upd_sfifo_pdata_err;
  logic                        ctr_drbg_upd_sfifo_final_err_sum;
  logic [2:0]                  ctr_drbg_upd_sfifo_final_err;
  logic                        ctr_drbg_gen_sfifo_gbencack_err_sum;
  logic [2:0]                  ctr_drbg_gen_sfifo_gbencack_err;
  logic                        ctr_drbg_gen_sfifo_grcstage_err_sum;
  logic [2:0]                  ctr_drbg_gen_sfifo_grcstage_err;
  logic                        ctr_drbg_gen_sfifo_ggenreq_err_sum;
  logic [2:0]                  ctr_drbg_gen_sfifo_ggenreq_err;
  logic                        ctr_drbg_gen_sfifo_gadstage_err_sum;
  logic [2:0]                  ctr_drbg_gen_sfifo_gadstage_err;
  logic                        ctr_drbg_gen_sfifo_ggenbits_err_sum;
  logic [2:0]                  ctr_drbg_gen_sfifo_ggenbits_err;
  logic                        block_encrypt_sfifo_blkenc_err_sum;
  logic [2:0]                  block_encrypt_sfifo_blkenc_err;
  logic                        cmd_gen_cnt_err_sum;
  logic                        cmd_stage_sm_err_sum;
  logic                        main_sm_err_sum;
  logic                        cs_main_sm_alert;
  logic                        cs_main_sm_err;
  logic [MainSmStateWidth-1:0] cs_main_sm_state;
  logic                        drbg_gen_sm_err_sum;
  logic                        drbg_gen_sm_err;
  logic                        drbg_updbe_sm_err_sum;
  logic                        drbg_updbe_sm_err;
  logic                        drbg_updob_sm_err_sum;
  logic                        drbg_updob_sm_err;
  logic                        aes_cipher_sm_err_sum;
  logic                        aes_cipher_sm_err;
  logic                        fifo_write_err_sum;
  logic                        fifo_read_err_sum;
  logic                        fifo_status_err_sum;

  logic [KeyLen-1:0]           state_db_rd_key;
  logic [BlkLen-1:0]           state_db_rd_v;
  logic [CtrLen-1:0]           state_db_rd_rc;
  logic                        state_db_rd_fips;
  logic [2:0]                  acmd_hold;
  logic [3:0]                  shid;
  logic                        gen_last;
  mubi4_t                      flag0;

  // blk encrypt arbiter
  logic [Cmd-1:0]              updblk_benblk_cmd_arb_din;
  logic [StateId-1:0]          updblk_benblk_id_arb_din;
  logic [BlkLen-1:0]           updblk_benblk_v_arb_din;
  logic [KeyLen-1:0]           updblk_benblk_key_arb_din;
  logic                        updblk_benblk_arb_req;
  logic                        updblk_benblk_arb_req_rdy;
  logic                        benblk_updblk_ack;
  logic                        updblk_benblk_ack_rdy;

  logic [Cmd-1:0]              genblk_benblk_cmd_arb_din;
  logic [StateId-1:0]          genblk_benblk_id_arb_din;
  logic [BlkLen-1:0]           genblk_benblk_v_arb_din;
  logic [KeyLen-1:0]           genblk_benblk_key_arb_din;
  logic                        genblk_benblk_arb_req;
  logic                        genblk_benblk_arb_req_rdy;
  logic                        benblk_genblk_ack;
  logic                        genblk_benblk_ack_rdy;

  logic [BlkEncArbWidth-1:0]   benblk_arb_din [2];
  logic [BlkEncArbWidth-1:0]   benblk_arb_data;
  logic [KeyLen-1:0]           benblk_arb_key;
  logic [BlkLen-1:0]           benblk_arb_v;
  logic [StateId-1:0]          benblk_arb_inst_id;
  logic [Cmd-1:0]              benblk_arb_cmd;
  logic                        benblk_arb_vld;
  logic                        benblk_ack;
  logic                        benblk_ack_rdy;
  logic                        benblk_arb_rdy;
  logic [Cmd-1:0]              benblk_cmd;
  logic [StateId-1:0]          benblk_inst_id;
  logic [BlkLen-1:0]           benblk_v;

  // update arbiter
  logic [Cmd-1:0]              cmdblk_updblk_ccmd_arb_din;
  logic [StateId-1:0]          cmdblk_updblk_id_arb_din;
  logic [BlkLen-1:0]           cmdblk_updblk_v_arb_din;
  logic [KeyLen-1:0]           cmdblk_updblk_key_arb_din;
  logic [SeedLen-1:0]          cmdblk_updblk_pdata_arb_din;
  logic                        cmdblk_updblk_arb_req;
  logic                        updblk_cmdblk_arb_req_rdy;
  logic                        updblk_cmdblk_ack;
  logic                        cmdblk_updblk_ack_rdy;

  logic [Cmd-1:0]              genblk_updblk_ccmd_arb_din;
  logic [StateId-1:0]          genblk_updblk_id_arb_din;
  logic [BlkLen-1:0]           genblk_updblk_v_arb_din;
  logic [KeyLen-1:0]           genblk_updblk_key_arb_din;
  logic [SeedLen-1:0]          genblk_updblk_pdata_arb_din;
  logic                        genblk_updblk_arb_req;
  logic                        updblk_genblk_arb_req_rdy;
  logic                        updblk_genblk_ack;
  logic                        genblk_updblk_ack_rdy;

  logic [UpdateArbWidth-1:0]   updblk_arb_din [2];
  logic [UpdateArbWidth-1:0]   updblk_arb_data;
  logic [KeyLen-1:0]           updblk_arb_key;
  logic [BlkLen-1:0]           updblk_arb_v;
  logic [SeedLen-1:0]          updblk_arb_pdata;
  logic [StateId-1:0]          updblk_arb_inst_id;
  logic [Cmd-1:0]              updblk_arb_ccmd;
  logic                        updblk_arb_vld;
  logic                        updblk_ack;
  logic                        updblk_ack_rdy;
  logic                        updblk_arb_rdy;
  logic [Cmd-1:0]              updblk_ccmd;
  logic [StateId-1:0]          updblk_inst_id;
  logic [KeyLen-1:0]           updblk_key;
  logic [BlkLen-1:0]           updblk_v;

  logic [2:0]                  cmd_stage_sfifo_cmd_err[NApps];
  logic [NApps-1:0]            cmd_stage_sfifo_cmd_err_sum;
  logic [NApps-1:0]            cmd_stage_sfifo_cmd_err_wr;
  logic [NApps-1:0]            cmd_stage_sfifo_cmd_err_rd;
  logic [NApps-1:0]            cmd_stage_sfifo_cmd_err_st;
  logic [2:0]                  cmd_stage_sfifo_genbits_err[NApps];
  logic [NApps-1:0]            cmd_stage_sfifo_genbits_err_sum;
  logic [NApps-1:0]            cmd_stage_sfifo_genbits_err_wr;
  logic [NApps-1:0]            cmd_stage_sfifo_genbits_err_rd;
  logic [NApps-1:0]            cmd_stage_sfifo_genbits_err_st;
  logic [NApps-1:0]            cmd_gen_cnt_err;
  logic [NApps-1:0]            cmd_stage_sm_err;
  logic                        ctr_drbg_upd_v_ctr_err;
  logic                        ctr_drbg_gen_v_ctr_err;

  logic [NApps-1:0]          cmd_stage_vld;
  logic [StateId-1:0]        cmd_stage_shid[NApps];
  logic [AppCmdWidth-1:0]    cmd_stage_bus[NApps];
  logic [NApps-1:0]          cmd_stage_rdy;
  logic [NApps-1:0]          cmd_arb_req;
  logic [NApps-1:0]          cmd_arb_gnt;
  logic [$clog2(NApps)-1:0]  cmd_arb_idx;
  logic [NApps-1:0]          cmd_arb_sop;
  logic [NApps-1:0]          cmd_arb_mop;
  logic [NApps-1:0]          cmd_arb_eop;
  logic [AppCmdWidth-1:0]    cmd_arb_bus[NApps];
  logic [NApps-1:0]          cmd_core_ack;
  logic [NApps-1:0]          cmd_core_ack_sts;
  logic [NApps-1:0]          cmd_stage_ack;
  logic [NApps-1:0]          cmd_stage_ack_sts;
  logic [NApps-1:0]          genbits_core_vld;
  logic [GenBitsWidth-1:0]   genbits_core_bus[NApps];
  logic [NApps-1:0]          genbits_core_fips;
  logic [NApps-1:0]          genbits_stage_vld;
  logic [NApps-1:0]          genbits_stage_fips;
  logic [GenBitsWidth-1:0]   genbits_stage_bus[NApps];
  logic [NApps-1:0]          genbits_stage_rdy;
  logic                      genbits_stage_vldo_sw;
  logic                      genbits_stage_bus_rd_sw;
  logic [31:0]               genbits_stage_bus_sw;
  logic                      genbits_stage_fips_sw;

  logic [15:0]               hw_exception_sts;
  logic [LcHwDebugCopies-1:0]lc_hw_debug_on_fo;
  logic                      state_db_is_dump_en;
  logic                      state_db_reg_rd_sel;
  logic                      state_db_reg_rd_id_pulse;
  logic [StateId-1:0]        state_db_reg_rd_id;
  logic [31:0]               state_db_reg_rd_val;

  logic [30:0]               err_code_test_bit;
  logic                      ctr_drbg_upd_es_ack;
  logic                      ctr_drbg_gen_es_ack;
  logic                      block_encrypt_quiet;

  logic                      cs_rdata_capt_vld;
  logic                      cs_bus_cmp_alert;
  logic                      cmd_rdy;
  logic [1:0]                efuse_sw_app_enable;

  logic                      unused_err_code_test_bit;
  logic                      unused_reg2hw_genbits;
  logic                      unused_int_state_val;

  prim_mubi_pkg::mubi8_t [1:0] en_csrng_sw_app_read;
  prim_mubi_pkg::mubi4_t [CsEnableCopies-1:0] mubi_cs_enable_fanout;
  prim_mubi_pkg::mubi4_t [Flag0Copies-1:0] mubi_flag0_fanout;

  // flops
  logic [2:0]                acmd_q, acmd_d;
  logic [3:0]                shid_q, shid_d;
  logic                      gen_last_q, gen_last_d;
  mubi4_t                    flag0_q, flag0_d;
  logic [$clog2(NApps)-1:0]  cmd_arb_idx_q, cmd_arb_idx_d;
  logic                      statedb_wr_select_q, statedb_wr_select_d;
  logic                      genbits_stage_fips_sw_q, genbits_stage_fips_sw_d;
  logic                      cmd_req_dly_q, cmd_req_dly_d;
  logic [Cmd-1:0]            cmd_req_ccmd_dly_q, cmd_req_ccmd_dly_d;
  logic                      cs_aes_halt_q, cs_aes_halt_d;
  logic [SeedLen-1:0]        entropy_src_seed_q, entropy_src_seed_d;
  logic                      entropy_src_fips_q, entropy_src_fips_d;
  logic [63:0]               cs_rdata_capt_q, cs_rdata_capt_d;
  logic                      cs_rdata_capt_vld_q, cs_rdata_capt_vld_d;
  logic                      sw_rdy_sts_q, sw_rdy_sts_d;

  always_ff @(posedge clk_i or negedge rst_ni)
    if (!rst_ni) begin
      acmd_q                  <= '0;
      shid_q                  <= '0;
      gen_last_q              <= '0;
      flag0_q                 <= prim_mubi_pkg::MuBi4False;
      cmd_arb_idx_q           <= '0;
      statedb_wr_select_q     <= '0;
      genbits_stage_fips_sw_q <= '0;
      cmd_req_dly_q           <= '0;
      cmd_req_ccmd_dly_q      <= '0;
      cs_aes_halt_q           <= '0;
      entropy_src_seed_q      <= '0;
      entropy_src_fips_q      <= '0;
      cs_rdata_capt_q         <= '0;
      cs_rdata_capt_vld_q     <= '0;
      sw_rdy_sts_q            <= '0;
    end else begin
      acmd_q                  <= acmd_d;
      shid_q                  <= shid_d;
      gen_last_q              <= gen_last_d;
      flag0_q                 <= flag0_d;
      cmd_arb_idx_q           <= cmd_arb_idx_d;
      statedb_wr_select_q     <= statedb_wr_select_d;
      genbits_stage_fips_sw_q <= genbits_stage_fips_sw_d;
      cmd_req_dly_q           <= cmd_req_dly_d;
      cmd_req_ccmd_dly_q      <= cmd_req_ccmd_dly_d;
      cs_aes_halt_q           <= cs_aes_halt_d;
      entropy_src_seed_q      <= entropy_src_seed_d;
      entropy_src_fips_q      <= entropy_src_fips_d;
      cs_rdata_capt_q         <= cs_rdata_capt_d;
      cs_rdata_capt_vld_q     <= cs_rdata_capt_vld_d;
      sw_rdy_sts_q            <= sw_rdy_sts_d;
    end

  //--------------------------------------------
  // instantiate interrupt hardware primitives
  //--------------------------------------------
  // All TLUL interrupts are collect in the section.

  prim_intr_hw #(
    .Width(1)
  ) u_intr_hw_cs_cmd_req_done (
    .clk_i                  (clk_i),
    .rst_ni                 (rst_ni),
    .event_intr_i           (event_cs_cmd_req_done),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.cs_cmd_req_done.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.cs_cmd_req_done.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.cs_cmd_req_done.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.cs_cmd_req_done.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.cs_cmd_req_done.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.cs_cmd_req_done.d),
    .intr_o                 (intr_cs_cmd_req_done_o)
  );

  prim_intr_hw #(
    .Width(1)
  ) u_intr_hw_cs_entropy_req (
    .clk_i                  (clk_i),
    .rst_ni                 (rst_ni),
    .event_intr_i           (event_cs_entropy_req),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.cs_entropy_req.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.cs_entropy_req.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.cs_entropy_req.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.cs_entropy_req.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.cs_entropy_req.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.cs_entropy_req.d),
    .intr_o                 (intr_cs_entropy_req_o)
  );


  prim_intr_hw #(
    .Width(1)
  ) u_intr_hw_cs_hw_inst_exc (
    .clk_i                  (clk_i),
    .rst_ni                 (rst_ni),
    .event_intr_i           (event_cs_hw_inst_exc),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.cs_hw_inst_exc.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.cs_hw_inst_exc.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.cs_hw_inst_exc.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.cs_hw_inst_exc.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.cs_hw_inst_exc.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.cs_hw_inst_exc.d),
    .intr_o                 (intr_cs_hw_inst_exc_o)
  );


  prim_intr_hw #(
    .Width(1)
  ) u_intr_hw_cs_fatal_err (
    .clk_i                  (clk_i),
    .rst_ni                 (rst_ni),
    .event_intr_i           (event_cs_fatal_err),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.cs_fatal_err.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.cs_fatal_err.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.cs_fatal_err.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.cs_fatal_err.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.cs_fatal_err.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.cs_fatal_err.d),
    .intr_o                 (intr_cs_fatal_err_o)
  );

  // set the interrupt sources
  assign event_cs_fatal_err = (cs_enable_fo[1]  && (
         (|cmd_stage_sfifo_cmd_err_sum) ||
         (|cmd_stage_sfifo_genbits_err_sum) ||
         ctr_drbg_cmd_sfifo_cmdreq_err_sum ||
         ctr_drbg_cmd_sfifo_rcstage_err_sum ||
         ctr_drbg_cmd_sfifo_keyvrc_err_sum ||
         ctr_drbg_upd_sfifo_updreq_err_sum ||
         ctr_drbg_upd_sfifo_bencreq_err_sum ||
         ctr_drbg_upd_sfifo_bencack_err_sum ||
         ctr_drbg_upd_sfifo_pdata_err_sum ||
         ctr_drbg_upd_sfifo_final_err_sum ||
         ctr_drbg_gen_sfifo_gbencack_err_sum ||
         ctr_drbg_gen_sfifo_grcstage_err_sum ||
         ctr_drbg_gen_sfifo_ggenreq_err_sum ||
         ctr_drbg_gen_sfifo_gadstage_err_sum ||
         ctr_drbg_gen_sfifo_ggenbits_err_sum ||
         block_encrypt_sfifo_blkenc_err_sum ||
         fifo_write_err_sum ||
         fifo_read_err_sum ||
         fifo_status_err_sum)) ||
         // errs not gated by cs_enable
         cmd_stage_sm_err_sum ||
         main_sm_err_sum ||
         drbg_gen_sm_err_sum ||
         drbg_updbe_sm_err_sum ||
         drbg_updob_sm_err_sum ||
         aes_cipher_sm_err_sum ||
         cmd_gen_cnt_err_sum;

  // set fifo errors that are single instances of source
  assign ctr_drbg_cmd_sfifo_cmdreq_err_sum = (|ctr_drbg_cmd_sfifo_cmdreq_err) ||
         err_code_test_bit[2];
  assign ctr_drbg_cmd_sfifo_rcstage_err_sum = (|ctr_drbg_cmd_sfifo_rcstage_err) ||
         err_code_test_bit[3];
  assign ctr_drbg_cmd_sfifo_keyvrc_err_sum = (|ctr_drbg_cmd_sfifo_keyvrc_err) ||
         err_code_test_bit[4];
  assign ctr_drbg_upd_sfifo_updreq_err_sum = (|ctr_drbg_upd_sfifo_updreq_err) ||
         err_code_test_bit[5];
  assign ctr_drbg_upd_sfifo_bencreq_err_sum = (|ctr_drbg_upd_sfifo_bencreq_err) ||
         err_code_test_bit[6];
  assign ctr_drbg_upd_sfifo_bencack_err_sum = (|ctr_drbg_upd_sfifo_bencack_err) ||
         err_code_test_bit[7];
  assign ctr_drbg_upd_sfifo_pdata_err_sum = (|ctr_drbg_upd_sfifo_pdata_err) ||
         err_code_test_bit[8];
  assign ctr_drbg_upd_sfifo_final_err_sum = (|ctr_drbg_upd_sfifo_final_err) ||
         err_code_test_bit[9];
  assign ctr_drbg_gen_sfifo_gbencack_err_sum = (|ctr_drbg_gen_sfifo_gbencack_err) ||
         err_code_test_bit[10];
  assign ctr_drbg_gen_sfifo_grcstage_err_sum = (|ctr_drbg_gen_sfifo_grcstage_err) ||
         err_code_test_bit[11];
  assign ctr_drbg_gen_sfifo_ggenreq_err_sum = (|ctr_drbg_gen_sfifo_ggenreq_err) ||
         err_code_test_bit[12];
  assign ctr_drbg_gen_sfifo_gadstage_err_sum = (|ctr_drbg_gen_sfifo_gadstage_err) ||
         err_code_test_bit[13];
  assign ctr_drbg_gen_sfifo_ggenbits_err_sum = (|ctr_drbg_gen_sfifo_ggenbits_err) ||
         err_code_test_bit[14];
  assign block_encrypt_sfifo_blkenc_err_sum = (|block_encrypt_sfifo_blkenc_err) ||
         err_code_test_bit[15];
  assign cmd_stage_sm_err_sum = (|cmd_stage_sm_err) ||
         err_code_test_bit[20];
  assign main_sm_err_sum = cs_main_sm_err ||
         err_code_test_bit[21];
  assign drbg_gen_sm_err_sum = drbg_gen_sm_err ||
         err_code_test_bit[22];
  assign drbg_updbe_sm_err_sum = drbg_updbe_sm_err ||
         err_code_test_bit[23];
  assign drbg_updob_sm_err_sum = drbg_updob_sm_err ||
         err_code_test_bit[24];
  assign aes_cipher_sm_err_sum = aes_cipher_sm_err ||
         err_code_test_bit[25];
  assign cmd_gen_cnt_err_sum = (|cmd_gen_cnt_err) || ctr_drbg_gen_v_ctr_err ||
         ctr_drbg_upd_v_ctr_err || err_code_test_bit[26];
  assign fifo_write_err_sum =
         block_encrypt_sfifo_blkenc_err[2] ||
         ctr_drbg_gen_sfifo_ggenbits_err[2] ||
         ctr_drbg_gen_sfifo_gadstage_err[2] ||
         ctr_drbg_gen_sfifo_ggenreq_err[2] ||
         ctr_drbg_gen_sfifo_grcstage_err[2] ||
         ctr_drbg_gen_sfifo_gbencack_err[2] ||
         ctr_drbg_upd_sfifo_final_err[2] ||
         ctr_drbg_upd_sfifo_pdata_err[2] ||
         ctr_drbg_upd_sfifo_bencack_err[2] ||
         ctr_drbg_upd_sfifo_bencreq_err[2] ||
         ctr_drbg_upd_sfifo_updreq_err[2] ||
         ctr_drbg_cmd_sfifo_keyvrc_err[2] ||
         ctr_drbg_cmd_sfifo_rcstage_err[2] ||
         ctr_drbg_cmd_sfifo_cmdreq_err[2] ||
         (|cmd_stage_sfifo_genbits_err_wr) ||
         (|cmd_stage_sfifo_cmd_err_wr) ||
         err_code_test_bit[28];
  assign fifo_read_err_sum =
         block_encrypt_sfifo_blkenc_err[1] ||
         ctr_drbg_gen_sfifo_ggenbits_err[1] ||
         ctr_drbg_gen_sfifo_gadstage_err[1] ||
         ctr_drbg_gen_sfifo_ggenreq_err[1] ||
         ctr_drbg_gen_sfifo_grcstage_err[1] ||
         ctr_drbg_gen_sfifo_gbencack_err[1] ||
         ctr_drbg_upd_sfifo_final_err[1] ||
         ctr_drbg_upd_sfifo_pdata_err[1] ||
         ctr_drbg_upd_sfifo_bencack_err[1] ||
         ctr_drbg_upd_sfifo_bencreq_err[1] ||
         ctr_drbg_upd_sfifo_updreq_err[1] ||
         ctr_drbg_cmd_sfifo_keyvrc_err[1] ||
         ctr_drbg_cmd_sfifo_rcstage_err[1] ||
         ctr_drbg_cmd_sfifo_cmdreq_err[1] ||
         (|cmd_stage_sfifo_genbits_err_rd) ||
         (|cmd_stage_sfifo_cmd_err_rd) ||
         err_code_test_bit[29];
  assign fifo_status_err_sum =
         block_encrypt_sfifo_blkenc_err[0] ||
         ctr_drbg_gen_sfifo_ggenbits_err[0] ||
         ctr_drbg_gen_sfifo_gadstage_err[0] ||
         ctr_drbg_gen_sfifo_ggenreq_err[0] ||
         ctr_drbg_gen_sfifo_grcstage_err[0] ||
         ctr_drbg_gen_sfifo_gbencack_err[0] ||
         ctr_drbg_upd_sfifo_final_err[0] ||
         ctr_drbg_upd_sfifo_pdata_err[0] ||
         ctr_drbg_upd_sfifo_bencack_err[0] ||
         ctr_drbg_upd_sfifo_bencreq_err[0] ||
         ctr_drbg_upd_sfifo_updreq_err[0] ||
         ctr_drbg_cmd_sfifo_keyvrc_err[0] ||
         ctr_drbg_cmd_sfifo_rcstage_err[0] ||
         ctr_drbg_cmd_sfifo_cmdreq_err[0] ||
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

  assign hw2reg.err_code.sfifo_cmdreq_err.d = 1'b1;
  assign hw2reg.err_code.sfifo_cmdreq_err.de = cs_enable_fo[4] &&
         ctr_drbg_cmd_sfifo_cmdreq_err_sum;

  assign hw2reg.err_code.sfifo_rcstage_err.d = 1'b1;
  assign hw2reg.err_code.sfifo_rcstage_err.de = cs_enable_fo[5] &&
         ctr_drbg_cmd_sfifo_rcstage_err_sum;

  assign hw2reg.err_code.sfifo_keyvrc_err.d = 1'b1;
  assign hw2reg.err_code.sfifo_keyvrc_err.de = cs_enable_fo[6] &&
         ctr_drbg_cmd_sfifo_keyvrc_err_sum;

  assign hw2reg.err_code.sfifo_updreq_err.d = 1'b1;
  assign hw2reg.err_code.sfifo_updreq_err.de = cs_enable_fo[7] &&
         ctr_drbg_upd_sfifo_updreq_err_sum;

  assign hw2reg.err_code.sfifo_bencreq_err.d = 1'b1;
  assign hw2reg.err_code.sfifo_bencreq_err.de = cs_enable_fo[8] &&
         ctr_drbg_upd_sfifo_bencreq_err_sum;

  assign hw2reg.err_code.sfifo_bencack_err.d = 1'b1;
  assign hw2reg.err_code.sfifo_bencack_err.de = cs_enable_fo[9] &&
         ctr_drbg_upd_sfifo_bencack_err_sum;

  assign hw2reg.err_code.sfifo_pdata_err.d = 1'b1;
  assign hw2reg.err_code.sfifo_pdata_err.de = cs_enable_fo[10] &&
         ctr_drbg_upd_sfifo_pdata_err_sum;

  assign hw2reg.err_code.sfifo_final_err.d = 1'b1;
  assign hw2reg.err_code.sfifo_final_err.de = cs_enable_fo[11] &&
         ctr_drbg_upd_sfifo_final_err_sum;

  assign hw2reg.err_code.sfifo_gbencack_err.d = 1'b1;
  assign hw2reg.err_code.sfifo_gbencack_err.de = cs_enable_fo[12] &&
         ctr_drbg_gen_sfifo_gbencack_err_sum;

  assign hw2reg.err_code.sfifo_grcstage_err.d = 1'b1;
  assign hw2reg.err_code.sfifo_grcstage_err.de = cs_enable_fo[13] &&
         ctr_drbg_gen_sfifo_grcstage_err_sum;

  assign hw2reg.err_code.sfifo_ggenreq_err.d = 1'b1;
  assign hw2reg.err_code.sfifo_ggenreq_err.de = cs_enable_fo[14] &&
         ctr_drbg_gen_sfifo_ggenreq_err_sum;

  assign hw2reg.err_code.sfifo_gadstage_err.d = 1'b1;
  assign hw2reg.err_code.sfifo_gadstage_err.de = cs_enable_fo[15] &&
         ctr_drbg_gen_sfifo_gadstage_err_sum;

  assign hw2reg.err_code.sfifo_ggenbits_err.d = 1'b1;
  assign hw2reg.err_code.sfifo_ggenbits_err.de = cs_enable_fo[16] &&
         ctr_drbg_gen_sfifo_ggenbits_err_sum;

  assign hw2reg.err_code.sfifo_blkenc_err.d = 1'b1;
  assign hw2reg.err_code.sfifo_blkenc_err.de = cs_enable_fo[17] &&
         block_encrypt_sfifo_blkenc_err_sum;

  assign hw2reg.err_code.cmd_stage_sm_err.d = 1'b1;
  assign hw2reg.err_code.cmd_stage_sm_err.de = cs_enable_fo[18] &&
         cmd_stage_sm_err_sum;

  assign hw2reg.err_code.main_sm_err.d = 1'b1;
  assign hw2reg.err_code.main_sm_err.de = cs_enable_fo[19] &&
         main_sm_err_sum;

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
         aes_cipher_sm_err_sum;

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
         cs_main_sm_alert ||
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


  // master module enable
  assign sw_app_enable = sw_app_enable_pfe;
  assign read_int_state = read_int_state_pfe;

  //------------------------------------------
  // application interface
  //------------------------------------------
  // Each application port has its own
  // csrng_cmd_stage block to recieve the
  // command, track the state of its completion,
  // and return any genbits if the command
  // is a generate command.

  for (genvar ai = 0; ai < NApps; ai = ai+1) begin : gen_cmd_stage

    csrng_cmd_stage #(
      .CmdFifoWidth(AppCmdWidth),
      .CmdFifoDepth(AppCmdFifoDepth),
      .StateId(StateId)
    ) u_csrng_cmd_stage (
      .clk_i                        (clk_i),
      .rst_ni                       (rst_ni),
      .cs_enable_i                  (cs_enable_fo[27]),
      .cmd_stage_vld_i              (cmd_stage_vld[ai]),
      .cmd_stage_shid_i             (cmd_stage_shid[ai]),
      .cmd_stage_bus_i              (cmd_stage_bus[ai]),
      .cmd_stage_rdy_o              (cmd_stage_rdy[ai]),
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

  end : gen_cmd_stage

  // SW interface connection (only 1, and must be present)
  // cmd req
  assign cmd_stage_vld[NApps-1] = reg2hw.cmd_req.qe;
  assign cmd_stage_shid[NApps-1] = StateId'(NApps-1);
  assign cmd_stage_bus[NApps-1] = reg2hw.cmd_req.q;
  assign hw2reg.sw_cmd_sts.cmd_rdy.de = 1'b1;
  assign hw2reg.sw_cmd_sts.cmd_rdy.d = cmd_rdy;
  assign cmd_rdy = !cmd_stage_vld[NApps-1] && sw_rdy_sts_q;
  assign sw_rdy_sts_d =
         !cs_enable_fo[28] ? 1'b1 :
         cmd_stage_vld[NApps-1] ? 1'b0 :
         cmd_stage_rdy[NApps-1] ? 1'b1 :
         sw_rdy_sts_q;

  // cmd ack sts
  assign hw2reg.sw_cmd_sts.cmd_sts.de = cmd_stage_ack[NApps-1];
  assign hw2reg.sw_cmd_sts.cmd_sts.d = cmd_stage_ack_sts[NApps-1];
  // genbits
  assign hw2reg.genbits_vld.genbits_vld.d = genbits_stage_vldo_sw;
  assign hw2reg.genbits_vld.genbits_fips.d = genbits_stage_fips_sw;
  assign hw2reg.genbits.d = (sw_app_enable && efuse_sw_app_enable[0]) ? genbits_stage_bus_sw : '0;
  assign genbits_stage_bus_rd_sw = reg2hw.genbits.re;

  assign efuse_sw_app_enable[0] = prim_mubi_pkg::mubi8_test_true_strict(en_csrng_sw_app_read[0]);
  assign efuse_sw_app_enable[1] = prim_mubi_pkg::mubi8_test_true_strict(en_csrng_sw_app_read[1]);

  prim_mubi8_sync #(
    .NumCopies(2),
    .AsyncOn(1)
  ) u_prim_mubi8_sync_sw_app_read (
    .clk_i,
    .rst_ni,
    .mubi_i(otp_en_csrng_sw_app_read_i),
    .mubi_o(en_csrng_sw_app_read)
  );

  // pack the gen bits into a 32 bit register sized word

  prim_packer_fifo #(
    .InW(BlkLen),
    .OutW(32),
    .ClearOnRead(1'b0)
  ) u_prim_packer_fifo_sw_genbits (
    .clk_i    (clk_i),
    .rst_ni   (rst_ni),
    .clr_i    (!cs_enable_fo[29]),
    .wvalid_i (genbits_stage_vld[NApps-1]),
    .wdata_i  (genbits_stage_bus[NApps-1]),
    .wready_o (genbits_stage_rdy[NApps-1]),
    .rvalid_o (genbits_stage_vldo_sw),
    .rdata_o  (genbits_stage_bus_sw),
    .rready_i (genbits_stage_bus_rd_sw),
    .depth_o  ()
  );

  // flops for SW fips status
  assign genbits_stage_fips_sw_d =
         (!cs_enable_fo[30]) ? 1'b0 :
         (genbits_stage_rdy[NApps-1] && genbits_stage_vld[NApps-1]) ? genbits_stage_fips[NApps-1] :
         genbits_stage_fips_sw_q;

  assign genbits_stage_fips_sw = genbits_stage_fips_sw_q;


  //--------------------------------------------
  // data path integrity check
  // - a countermeasure to detect entropy bus tampering attempts
  // - checks to make sure repeated data sets off
  //   an alert for sw to handle
  //--------------------------------------------

  // SEC_CM: SW_GENBITS.BUS.CONSISTENCY

  // capture a copy of the genbits data
  assign cs_rdata_capt_vld = (genbits_stage_vld[NApps-1] && genbits_stage_rdy[NApps-1]);

  assign cs_rdata_capt_d = cs_rdata_capt_vld ? genbits_stage_bus[NApps-1][63:0] : cs_rdata_capt_q;

  assign cs_rdata_capt_vld_d =
         !cs_enable_fo[31] ? 1'b0 :
         cs_rdata_capt_vld ? 1'b1 :
         cs_rdata_capt_vld_q;

  // continuous compare of the entropy data for sw port
  assign cs_bus_cmp_alert = cs_rdata_capt_vld && cs_rdata_capt_vld_q &&
         (cs_rdata_capt_q == genbits_stage_bus[NApps-1][63:0]); // only look at 64 bits

  assign hw2reg.recov_alert_sts.cs_bus_cmp_alert.de = cs_bus_cmp_alert;
  assign hw2reg.recov_alert_sts.cs_bus_cmp_alert.d  = cs_bus_cmp_alert;

  assign hw2reg.recov_alert_sts.cs_main_sm_alert.de = cs_main_sm_alert;
  assign hw2reg.recov_alert_sts.cs_main_sm_alert.d  = cs_main_sm_alert;


  // HW interface connections (up to 16, numbered 0-14)
  for (genvar hai = 0; hai < (NApps-1); hai = hai+1) begin : gen_app_if
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
    assign csrng_cmd_o[hai].genbits_bus = genbits_stage_vld[hai] ? genbits_stage_bus[hai] : '0;
    assign genbits_stage_rdy[hai] = csrng_cmd_i[hai].genbits_ready;
  end : gen_app_if

  // set ack status for configured instances
  for (genvar i = 0; i < NHwApps; i = i+1) begin : gen_app_if_sts
    assign hw_exception_sts[i] = cmd_stage_ack[i] && cmd_stage_ack_sts[i];
  end : gen_app_if_sts

  // set ack status to zero for un-configured instances
  for (genvar i = NHwApps; i < 16; i = i+1) begin : gen_app_if_zero_sts
    assign hw_exception_sts[i] = 1'b0;
  end : gen_app_if_zero_sts

  // set fifo err status bits
  for (genvar i = 0; i < NApps; i = i+1) begin : gen_fifo_sts
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
    .N(NApps),  // Number of request ports
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

  mubi4_t mubi_acmd_flag0;
  assign mubi_acmd_flag0 = mubi4_t'(acmd_bus[11:8]);
  assign acmd_flag0_pfa = mubi4_test_invalid(flag0_q);
  assign hw2reg.recov_alert_sts.acmd_flag0_field_alert.de = acmd_flag0_pfa;
  assign hw2reg.recov_alert_sts.acmd_flag0_field_alert.d  = acmd_flag0_pfa;

  // parse the command bus
  assign acmd_hold = acmd_sop ? acmd_bus[2:0] : acmd_q;
  assign flag0 = mubi_acmd_flag0;
  assign shid = acmd_bus[15:12];
  assign gen_last = acmd_bus[16];

  assign acmd_d =
         (!cs_enable_fo[32]) ? '0 :
         acmd_sop ? acmd_bus[2:0] :
         acmd_q;

  assign shid_d =
         (!cs_enable_fo[33]) ? '0 :
         acmd_sop ? shid :
         shid_q;

  assign gen_last_d =
         (!cs_enable_fo[34]) ? '0 :
         acmd_sop ? gen_last :
         gen_last_q;

  assign flag0_d =
         (!cs_enable_fo[35]) ? prim_mubi_pkg::MuBi4False :
         (acmd_sop && ((acmd_bus[2:0] == INS) || (acmd_bus[2:0] == RES))) ? flag0 :
         flag0_q;

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
    .clk_i                  (clk_i),
    .rst_ni                 (rst_ni),
    .enable_i               (cs_enable_fo[36]),
    .acmd_avail_i           (acmd_avail),
    .acmd_accept_o          (acmd_accept),
    .acmd_i                 (acmd_hold),
    .acmd_eop_i             (acmd_eop),
    .ctr_drbg_cmd_req_rdy_i (ctr_drbg_cmd_req_rdy),
    .flag0_i                (flag0_fo[0]),
    .cmd_entropy_req_o      (cmd_entropy_req),
    .cmd_entropy_avail_i    (cmd_entropy_avail),
    .instant_req_o          (instant_req),
    .reseed_req_o           (reseed_req),
    .generate_req_o         (generate_req),
    .update_req_o           (update_req),
    .uninstant_req_o        (uninstant_req),
    .clr_adata_packer_o     (clr_adata_packer),
    .cmd_complete_i         (state_db_wr_req),
    .local_escalate_i       (cmd_gen_cnt_err_sum),
    .main_sm_state_o        (cs_main_sm_state),
    .main_sm_alert_o        (cs_main_sm_alert),
    .main_sm_err_o          (cs_main_sm_err)
  );

  // interrupt for sw app interface only
  assign event_cs_cmd_req_done = cmd_stage_ack[NApps-1];

  // interrupt for entropy request
  assign event_cs_entropy_req = entropy_src_hw_if_o.es_req;

  // interrupt for app interface exception
  assign event_cs_hw_inst_exc = |hw_exception_sts;

  // entropy available
  assign cmd_entropy_avail = entropy_src_hw_if_i.es_ack;

  for (genvar csi = 0; csi < NApps; csi = csi+1) begin : gen_cmd_ack
    assign cmd_core_ack[csi] = state_db_sts_ack && (state_db_sts_id == csi);
    assign cmd_core_ack_sts[csi] = state_db_sts_sts;
    assign genbits_core_vld[csi] = gen_result_wr_req && (gen_result_inst_id == csi);
    assign genbits_core_bus[csi] = gen_result_bits;
    assign genbits_core_fips[csi] = gen_result_fips;
  end : gen_cmd_ack


  prim_packer_fifo #(
    .InW(32),
    .OutW(SeedLen),
    .ClearOnRead(1'b1)
  ) u_prim_packer_fifo_adata (
    .clk_i      (clk_i),
    .rst_ni     (rst_ni),
    .clr_i      (!cs_enable_fo[37] || packer_adata_clr),
    .wvalid_i   (acmd_mop),
    .wdata_i    (acmd_bus),
    .wready_o   (),
    .rvalid_o   (),
    .rdata_o    (packer_adata),
    .rready_i   (packer_adata_pop),
    .depth_o    (packer_adata_depth)
  );

  assign packer_adata_pop = cs_enable_fo[38] &&
         clr_adata_packer && (packer_adata_depth == ADataDepthClog'(MaxClen));

  assign packer_adata_clr = cs_enable_fo[39] &&
         clr_adata_packer && (packer_adata_depth < ADataDepthClog'(MaxClen));

  //-------------------------------------
  // csrng_state_db nstantiation
  //-------------------------------------
  // This block holds the internal state
  // of each csrng instance. The state
  // is updated after each command.

  assign cmd_result_wr_req = cmd_result_ack && (cmd_result_ccmd != GEN);

  // register read access
  assign state_db_reg_rd_sel = reg2hw.int_state_val.re;
  assign state_db_reg_rd_id = reg2hw.int_state_num.q;
  assign state_db_reg_rd_id_pulse = reg2hw.int_state_num.qe;
  assign hw2reg.int_state_val.d = state_db_reg_rd_val;
  assign state_db_is_dump_en = cs_enable_fo[40] && read_int_state && efuse_sw_app_enable[1];


  csrng_state_db #(
    .NApps(NApps),
    .StateId(StateId),
    .BlkLen(BlkLen),
    .KeyLen(KeyLen),
    .CtrLen(CtrLen),
    .Cmd(Cmd)
  ) u_csrng_state_db (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .state_db_enable_i(cs_enable_fo[41]),
    .state_db_rd_inst_id_i(shid_q),
    .state_db_rd_key_o(state_db_rd_key),
    .state_db_rd_v_o(state_db_rd_v),
    .state_db_rd_res_ctr_o(state_db_rd_rc),
    .state_db_rd_inst_st_o(), // NC
    .state_db_rd_fips_o(state_db_rd_fips),

    .state_db_wr_req_i(state_db_wr_req),
    .state_db_wr_req_rdy_o(state_db_wr_req_rdy),
    .state_db_wr_inst_id_i(state_db_wr_inst_id),
    .state_db_wr_fips_i(state_db_wr_fips),
    .state_db_wr_ccmd_i(state_db_wr_ccmd),
    .state_db_wr_key_i(state_db_wr_key),
    .state_db_wr_v_i(state_db_wr_v),
    .state_db_wr_res_ctr_i(state_db_wr_rc),
    .state_db_wr_sts_i(state_db_wr_sts),

    .state_db_is_dump_en_i(state_db_is_dump_en),
    .state_db_reg_rd_sel_i(state_db_reg_rd_sel),
    .state_db_reg_rd_id_pulse_i(state_db_reg_rd_id_pulse),
    .state_db_reg_rd_id_i(state_db_reg_rd_id),
    .state_db_reg_rd_val_o(state_db_reg_rd_val),
    .state_db_sts_ack_o(state_db_sts_ack),
    .state_db_sts_sts_o(state_db_sts_sts),
    .state_db_sts_id_o(state_db_sts_id)
  );

  assign statedb_wr_select_d =
         (!cs_enable_fo[42]) ? '0 :
         !statedb_wr_select_q;

  assign cmd_blk_select = !statedb_wr_select_q;
  assign gen_blk_select =  statedb_wr_select_q;

  // return to requesting block
  assign cmd_result_ack_rdy = (cmd_blk_select && state_db_wr_req_rdy) && ctr_drbg_gen_req_rdy;
  assign gen_result_ack_rdy = gen_blk_select && state_db_wr_req_rdy;

  // muxes for statedb block inputs
  assign state_db_wr_req = gen_blk_select ? gen_result_wr_req : cmd_result_wr_req;
  assign state_db_wr_inst_id = gen_blk_select ? gen_result_inst_id : cmd_result_inst_id;
  assign state_db_wr_fips = gen_blk_select ? gen_result_fips : cmd_result_fips;
  assign state_db_wr_ccmd = gen_blk_select ?  gen_result_ccmd : cmd_result_ccmd;
  assign state_db_wr_key = gen_blk_select ? gen_result_key : cmd_result_key;
  assign state_db_wr_v = gen_blk_select ? gen_result_v : cmd_result_v;
  assign state_db_wr_rc = gen_blk_select ? gen_result_rc : cmd_result_rc;
  assign state_db_wr_sts = gen_blk_select ? gen_result_ack_sts : cmd_result_ack_sts;


  //--------------------------------------------
  // entropy interface
  //--------------------------------------------
  // Basic interface logic with the entropy_src block

  assign entropy_src_hw_if_o.es_req = cs_enable_fo[43] &&
         cmd_entropy_req;


  // SEC_CM: CONSTANTS.LC_GATED
  assign seed_diversification = lc_hw_debug_on_fo[0] ? RndCnstCsKeymgrDivNonProduction :
                                                       RndCnstCsKeymgrDivProduction;

  // Capture entropy from entropy_src
  assign entropy_src_seed_d =
         ~cs_enable_fo[51] ? '0 :
         cmd_req_dly_q ? '0 :                  // reset after every cmd
         (cmd_entropy_avail && flag0_fo[1]) ? '0 : // special case where zero is used
         cmd_entropy_avail ? (entropy_src_hw_if_i.es_bits ^ seed_diversification) :
         entropy_src_seed_q;
  assign entropy_src_fips_d =
         ~cs_enable_fo[52] ? '0 :
         cmd_req_dly_q ? '0 :                  // reset after every cmd
         (cmd_entropy_avail && flag0_fo[2]) ? '0 : // special case where zero is used
         cmd_entropy_avail ? entropy_src_hw_if_i.es_fips :
         entropy_src_fips_q;

  assign cmd_entropy = entropy_src_seed_q;

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



  assign cmd_req_ccmd_dly_d =
         (!cs_enable_fo[44]) ? '0 :
         acmd_hold;

  assign ctr_drbg_cmd_ccmd = cmd_req_ccmd_dly_q;


  assign cmd_req_dly_d =
         (!cs_enable_fo[45]) ? '0 :
         (instant_req || reseed_req || generate_req || update_req || uninstant_req);

  assign ctr_drbg_cmd_req = cmd_req_dly_q;

  csrng_ctr_drbg_cmd #(
    .Cmd(Cmd),
    .StateId(StateId),
    .BlkLen(BlkLen),
    .KeyLen(KeyLen),
    .SeedLen(SeedLen),
    .CtrLen(CtrLen)
  ) u_csrng_ctr_drbg_cmd (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .ctr_drbg_cmd_enable_i(cs_enable_fo[46]),
    .ctr_drbg_cmd_req_i(ctr_drbg_cmd_req),
    .ctr_drbg_cmd_rdy_o(ctr_drbg_cmd_req_rdy),
    .ctr_drbg_cmd_ccmd_i(ctr_drbg_cmd_ccmd),
    .ctr_drbg_cmd_inst_id_i(shid_q),
    .ctr_drbg_cmd_glast_i(gen_last_q),
    .ctr_drbg_cmd_entropy_i(cmd_entropy),
    .ctr_drbg_cmd_entropy_fips_i(cmd_entropy_fips), // send to state_db
    .ctr_drbg_cmd_adata_i(packer_adata),
    .ctr_drbg_cmd_key_i(state_db_rd_key),
    .ctr_drbg_cmd_v_i(state_db_rd_v),
    .ctr_drbg_cmd_rc_i(state_db_rd_rc),
    .ctr_drbg_cmd_fips_i(state_db_rd_fips), // send to genbits user

    .ctr_drbg_cmd_ack_o(cmd_result_ack),
    .ctr_drbg_cmd_sts_o(cmd_result_ack_sts),
    .ctr_drbg_cmd_rdy_i(cmd_result_ack_rdy),
    .ctr_drbg_cmd_ccmd_o(cmd_result_ccmd),
    .ctr_drbg_cmd_inst_id_o(cmd_result_inst_id),
    .ctr_drbg_cmd_glast_o(cmd_result_glast),
    .ctr_drbg_cmd_fips_o(cmd_result_fips),
    .ctr_drbg_cmd_adata_o(cmd_result_adata),
    .ctr_drbg_cmd_key_o(cmd_result_key),
    .ctr_drbg_cmd_v_o(cmd_result_v),
    .ctr_drbg_cmd_rc_o(cmd_result_rc),

    // interface to updblk from cmdblk
    .cmd_upd_req_o(cmdblk_updblk_arb_req),
    .upd_cmd_rdy_i(updblk_cmdblk_arb_req_rdy),
    .cmd_upd_ccmd_o(cmdblk_updblk_ccmd_arb_din),
    .cmd_upd_inst_id_o(cmdblk_updblk_id_arb_din),
    .cmd_upd_pdata_o(cmdblk_updblk_pdata_arb_din),
    .cmd_upd_key_o(cmdblk_updblk_key_arb_din),
    .cmd_upd_v_o(cmdblk_updblk_v_arb_din),

    .upd_cmd_ack_i(updblk_cmdblk_ack),
    .cmd_upd_rdy_o(cmdblk_updblk_ack_rdy),
    .upd_cmd_ccmd_i(updblk_ccmd),
    .upd_cmd_inst_id_i(updblk_inst_id),
    .upd_cmd_key_i(updblk_key),
    .upd_cmd_v_i(updblk_v),

    .ctr_drbg_cmd_sfifo_cmdreq_err_o(ctr_drbg_cmd_sfifo_cmdreq_err),
    .ctr_drbg_cmd_sfifo_rcstage_err_o(ctr_drbg_cmd_sfifo_rcstage_err),
    .ctr_drbg_cmd_sfifo_keyvrc_err_o(ctr_drbg_cmd_sfifo_keyvrc_err)
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


  csrng_ctr_drbg_upd #(
    .Cmd(Cmd),
    .StateId(StateId),
    .BlkLen(BlkLen),
    .KeyLen(KeyLen),
    .SeedLen(SeedLen),
    .CtrLen(CtrLen)
  ) u_csrng_ctr_drbg_upd (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .ctr_drbg_upd_enable_i(cs_enable_fo[47]),
    .ctr_drbg_upd_req_i(updblk_arb_vld),
    .ctr_drbg_upd_rdy_o(updblk_arb_rdy),
    .ctr_drbg_upd_ack_o(updblk_ack),
    .ctr_drbg_upd_rdy_i(updblk_ack_rdy),
    .ctr_drbg_upd_ccmd_i(updblk_arb_ccmd),
    .ctr_drbg_upd_inst_id_i(updblk_arb_inst_id),
    .ctr_drbg_upd_pdata_i(updblk_arb_pdata),
    .ctr_drbg_upd_key_i(updblk_arb_key),
    .ctr_drbg_upd_v_i(updblk_arb_v),
    .ctr_drbg_upd_ccmd_o(updblk_ccmd),
    .ctr_drbg_upd_inst_id_o(updblk_inst_id),
    .ctr_drbg_upd_key_o(updblk_key),
    .ctr_drbg_upd_v_o(updblk_v),

    // es halt interface
    .ctr_drbg_upd_es_req_i(cs_aes_halt_i.cs_aes_halt_req),
    .ctr_drbg_upd_es_ack_o(ctr_drbg_upd_es_ack),

    .block_encrypt_req_o(updblk_benblk_arb_req),
    .block_encrypt_rdy_i(updblk_benblk_arb_req_rdy),
    .block_encrypt_ccmd_o(updblk_benblk_cmd_arb_din),
    .block_encrypt_inst_id_o(updblk_benblk_id_arb_din),
    .block_encrypt_key_o(updblk_benblk_key_arb_din),
    .block_encrypt_v_o(updblk_benblk_v_arb_din),
    .block_encrypt_ack_i(benblk_updblk_ack),
    .block_encrypt_rdy_o(updblk_benblk_ack_rdy),
    .block_encrypt_ccmd_i(benblk_cmd),
    .block_encrypt_inst_id_i(benblk_inst_id),
    .block_encrypt_v_i(benblk_v),
    .ctr_drbg_upd_v_ctr_err_o(ctr_drbg_upd_v_ctr_err),
    .ctr_drbg_upd_sfifo_updreq_err_o(ctr_drbg_upd_sfifo_updreq_err),
    .ctr_drbg_upd_sfifo_bencreq_err_o(ctr_drbg_upd_sfifo_bencreq_err),
    .ctr_drbg_upd_sfifo_bencack_err_o(ctr_drbg_upd_sfifo_bencack_err),
    .ctr_drbg_upd_sfifo_pdata_err_o(ctr_drbg_upd_sfifo_pdata_err),
    .ctr_drbg_upd_sfifo_final_err_o(ctr_drbg_upd_sfifo_final_err),
    .ctr_drbg_updbe_sm_err_o(drbg_updbe_sm_err),
    .ctr_drbg_updob_sm_err_o(drbg_updob_sm_err)
  );

  // update block  arbiter

  prim_arbiter_ppc #(
    .N(NUpdateArbReqs), // (cmd req and gen req)
    .DW(UpdateArbWidth) // Data width
  ) u_prim_arbiter_ppc_updblk_arb (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .req_chk_i(cs_enable_fo[1]),
    .req_i({genblk_updblk_arb_req,cmdblk_updblk_arb_req}),
    .data_i(updblk_arb_din),
    .gnt_o({updblk_genblk_arb_req_rdy,updblk_cmdblk_arb_req_rdy}),
    .idx_o(),
    .valid_o(updblk_arb_vld),
    .data_o(updblk_arb_data),
    .ready_i(updblk_arb_rdy)
  );

  assign updblk_arb_din[0] = {cmdblk_updblk_key_arb_din,cmdblk_updblk_v_arb_din,
                              cmdblk_updblk_pdata_arb_din,
                              cmdblk_updblk_id_arb_din,cmdblk_updblk_ccmd_arb_din};

  assign updblk_arb_din[1] = {genblk_updblk_key_arb_din,genblk_updblk_v_arb_din,
                              genblk_updblk_pdata_arb_din,
                              genblk_updblk_id_arb_din,genblk_updblk_ccmd_arb_din};

  assign {updblk_arb_key,updblk_arb_v,updblk_arb_pdata,
          updblk_arb_inst_id,updblk_arb_ccmd} = updblk_arb_data;

  assign updblk_cmdblk_ack = (updblk_ack && (updblk_ccmd != GENU));
  assign updblk_genblk_ack = (updblk_ack && (updblk_ccmd == GENU));

  assign updblk_ack_rdy = (updblk_ccmd == GENU) ? genblk_updblk_ack_rdy : cmdblk_updblk_ack_rdy;


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
    assign lc_hw_debug_on_fo[i] = (lc_hw_debug_en_out[i] == lc_ctrl_pkg::On);
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
    .SBoxImpl(SBoxImpl),
    .Cmd(Cmd),
    .StateId(StateId),
    .BlkLen(BlkLen),
    .KeyLen(KeyLen)
  ) u_csrng_block_encrypt (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .block_encrypt_enable_i(cs_enable_fo[48]),
    .block_encrypt_req_i(benblk_arb_vld),
    .block_encrypt_rdy_o(benblk_arb_rdy),
    .block_encrypt_key_i(benblk_arb_key),
    .block_encrypt_v_i(benblk_arb_v),
    .block_encrypt_cmd_i(benblk_arb_cmd),
    .block_encrypt_id_i(benblk_arb_inst_id),
    .block_encrypt_ack_o(benblk_ack),
    .block_encrypt_rdy_i(benblk_ack_rdy),
    .block_encrypt_cmd_o(benblk_cmd),
    .block_encrypt_id_o(benblk_inst_id),
    .block_encrypt_v_o(benblk_v),
    .block_encrypt_quiet_o(block_encrypt_quiet),
    .block_encrypt_aes_cipher_sm_err_o(aes_cipher_sm_err),
    .block_encrypt_sfifo_blkenc_err_o(block_encrypt_sfifo_blkenc_err)
  );


  prim_arbiter_ppc #(
    .N(NBlkEncArbReqs), // (upd req and gen req)
    .DW(BlkEncArbWidth) // Data width
  ) u_prim_arbiter_ppc_benblk_arb (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .req_chk_i(cs_enable_fo[1]),
    .req_i({genblk_benblk_arb_req,updblk_benblk_arb_req}),
    .data_i(benblk_arb_din),
    .gnt_o({genblk_benblk_arb_req_rdy,updblk_benblk_arb_req_rdy}),
    .idx_o(),
    .valid_o(benblk_arb_vld),
    .data_o(benblk_arb_data),
    .ready_i(benblk_arb_rdy)
  );

  assign benblk_arb_din[0] = {updblk_benblk_key_arb_din,updblk_benblk_v_arb_din,
                              updblk_benblk_id_arb_din,updblk_benblk_cmd_arb_din};
  assign benblk_arb_din[1] = {genblk_benblk_key_arb_din,genblk_benblk_v_arb_din,
                              genblk_benblk_id_arb_din,genblk_benblk_cmd_arb_din};

  assign benblk_updblk_ack = (benblk_ack && (benblk_cmd != GENB));
  assign benblk_genblk_ack = (benblk_ack && (benblk_cmd == GENB));

  assign benblk_ack_rdy = (benblk_cmd == GENB) ? genblk_benblk_ack_rdy : updblk_benblk_ack_rdy;

  assign {benblk_arb_key,benblk_arb_v,benblk_arb_inst_id,benblk_arb_cmd} = benblk_arb_data;


  //-------------------------------------
  // csrng_ctr_drbg_gen instantiation
  //-------------------------------------
  // this block performs the second sequence
  // of the generate command. The first part
  // of the sequence is done by the
  // csrng_ctr_drbg_cmd block.

  assign ctr_drbg_gen_req = cmd_result_ack && (cmd_result_ccmd == GEN);


  csrng_ctr_drbg_gen #(
    .NApps(NApps),
    .Cmd(Cmd),
    .StateId(StateId),
    .BlkLen(BlkLen),
    .KeyLen(KeyLen),
    .SeedLen(SeedLen),
    .CtrLen(CtrLen)
  ) u_csrng_ctr_drbg_gen (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .ctr_drbg_gen_enable_i(cs_enable_fo[49]),
    .ctr_drbg_gen_req_i(ctr_drbg_gen_req),
    .ctr_drbg_gen_rdy_o(ctr_drbg_gen_req_rdy),
    .ctr_drbg_gen_ccmd_i(cmd_result_ccmd),
    .ctr_drbg_gen_inst_id_i(cmd_result_inst_id),
    .ctr_drbg_gen_glast_i(cmd_result_glast),
    .ctr_drbg_gen_fips_i(cmd_result_fips),
    .ctr_drbg_gen_adata_i(cmd_result_adata),
    .ctr_drbg_gen_key_i(cmd_result_key),
    .ctr_drbg_gen_v_i(cmd_result_v),
    .ctr_drbg_gen_rc_i(cmd_result_rc),

    .ctr_drbg_gen_ack_o(gen_result_wr_req),
    .ctr_drbg_gen_sts_o(gen_result_ack_sts),
    .ctr_drbg_gen_rdy_i(gen_result_ack_rdy),
    .ctr_drbg_gen_ccmd_o(gen_result_ccmd),
    .ctr_drbg_gen_inst_id_o(gen_result_inst_id),
    .ctr_drbg_gen_fips_o(gen_result_fips),
    .ctr_drbg_gen_key_o(gen_result_key),
    .ctr_drbg_gen_v_o(gen_result_v),
    .ctr_drbg_gen_rc_o(gen_result_rc),
    .ctr_drbg_gen_bits_o(gen_result_bits),

    // es halt interface
    .ctr_drbg_gen_es_req_i(cs_aes_halt_i.cs_aes_halt_req),
    .ctr_drbg_gen_es_ack_o(ctr_drbg_gen_es_ack),

    // interface to updblk from genblk
    .gen_upd_req_o(genblk_updblk_arb_req),
    .upd_gen_rdy_i(updblk_genblk_arb_req_rdy),
    .gen_upd_ccmd_o(genblk_updblk_ccmd_arb_din),
    .gen_upd_inst_id_o(genblk_updblk_id_arb_din),
    .gen_upd_pdata_o(genblk_updblk_pdata_arb_din),
    .gen_upd_key_o(genblk_updblk_key_arb_din),
    .gen_upd_v_o(genblk_updblk_v_arb_din),

    .upd_gen_ack_i(updblk_genblk_ack),
    .gen_upd_rdy_o(genblk_updblk_ack_rdy),
    .upd_gen_ccmd_i(updblk_ccmd),
    .upd_gen_inst_id_i(updblk_inst_id),
    .upd_gen_key_i(updblk_key),
    .upd_gen_v_i(updblk_v),

    .block_encrypt_req_o(genblk_benblk_arb_req),
    .block_encrypt_rdy_i(genblk_benblk_arb_req_rdy),
    .block_encrypt_ccmd_o(genblk_benblk_cmd_arb_din),
    .block_encrypt_inst_id_o(genblk_benblk_id_arb_din),
    .block_encrypt_key_o(genblk_benblk_key_arb_din),
    .block_encrypt_v_o(genblk_benblk_v_arb_din),
    .block_encrypt_ack_i(benblk_genblk_ack),
    .block_encrypt_rdy_o(genblk_benblk_ack_rdy),
    .block_encrypt_ccmd_i(benblk_cmd),
    .block_encrypt_inst_id_i(benblk_inst_id),
    .block_encrypt_v_i(benblk_v),

    .ctr_drbg_gen_v_ctr_err_o(ctr_drbg_gen_v_ctr_err),
    .ctr_drbg_gen_sfifo_gbencack_err_o(ctr_drbg_gen_sfifo_gbencack_err),
    .ctr_drbg_gen_sfifo_grcstage_err_o(ctr_drbg_gen_sfifo_grcstage_err),
    .ctr_drbg_gen_sfifo_ggenreq_err_o(ctr_drbg_gen_sfifo_ggenreq_err),
    .ctr_drbg_gen_sfifo_gadstage_err_o(ctr_drbg_gen_sfifo_gadstage_err),
    .ctr_drbg_gen_sfifo_ggenbits_err_o(ctr_drbg_gen_sfifo_ggenbits_err),
    .ctr_drbg_gen_sm_err_o(drbg_gen_sm_err)
  );


  // es to cs halt request to reduce power spikes
  assign cs_aes_halt_d =
         (ctr_drbg_upd_es_ack && ctr_drbg_gen_es_ack && block_encrypt_quiet &&
          cs_aes_halt_i.cs_aes_halt_req && !cs_aes_halt_q);

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
  assign unused_err_code_test_bit = (|err_code_test_bit[19:16]) || (|err_code_test_bit[27:26]);
  assign unused_reg2hw_genbits = (|reg2hw.genbits.q);
  assign unused_int_state_val = (|reg2hw.int_state_val.q);


endmodule // csrng_core
