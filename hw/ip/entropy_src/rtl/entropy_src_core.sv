// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: entropy_src core module
//

module entropy_src_core import entropy_src_pkg::*; #(
  parameter int unsigned EsFifoDepth = 1024
) (
  input                  clk_i,
  input                  rst_ni,

  input  entropy_src_reg_pkg::entropy_src_reg2hw_t reg2hw,
  output entropy_src_reg_pkg::entropy_src_hw2reg_t hw2reg,

  // Efuse Interface
  input efuse_cs_sw_reg_en_i,


  // Entropy Interface
  input  entropy_src_hw_if_req_t entropy_src_hw_if_i,
  output entropy_src_hw_if_rsp_t entropy_src_hw_if_o,

  // Analog Interface
  input clk_es_50mhz_i,
  input rst_es_50mhz_ni,
  output es_mg_enable_o,
  input mg_es_ok_i,
  input [7:0] mg_bits_p_i,
  input [7:0] mg_bits_n_i,

  output logic           es_entropy_valid_o,
  output logic           es_ana_src_ok_o,
  output logic           es_ana_bits_err_o,
  output logic           es_ana_fifo_err_o,
  output logic           es_fifo_err_o
);

  import entropy_src_reg_pkg::*;

  localparam int unsigned AnFifoWidth = 8;
  localparam int unsigned AnFifoDepth = 4;

  // signals
  logic [7:0] es_entropy_bits;
  logic       es_entropy_bits_vld;
  logic [7:0] lfsr_value;
  logic [7:0]  seed_value;
  logic        load_seed;
  logic        es_enable;
  logic        es_enable_dig;
  logic        es_enable_ana;
  logic        lfsr_enable;
  logic        esentropy_rd_pls;
  logic        event_es_entropy_valid;
  logic        event_es_ana_src_ok;
  logic        event_es_ana_bits_err;
  logic        event_es_ana_fifo_err;
  logic        event_es_fifo_err;
  logic [15:0] es_rate;
  logic        es_rate_entropy_valid;
  logic [2:0]  es_reg_fifo_thresh;
  logic [2:0]  es_fifo_thresh;

  logic        sfifo_esdig_push;
  logic        sfifo_esdig_pop;
  logic        sfifo_esdig_clr;
  logic [7:0]  sfifo_esdig_wdata;
  logic [7:0]  sfifo_esdig_rdata;
  logic [2:0]  sfifo_esdig_depth;
  logic        sfifo_esdig_not_full;
  logic        sfifo_esdig_not_empty;
  logic        sfifo_esdig_err;

  logic        sfifo_quar0_push;
  logic        sfifo_quar0_pop;
  logic        sfifo_quar0_clr;
  logic [31:0] sfifo_quar0_wdata;
  logic [31:0] sfifo_quar0_rdata;
  logic        sfifo_quar0_not_full;
  logic        sfifo_quar0_not_empty;
  logic        sfifo_quar0_err;

  logic        sfifo_quar1_push;
  logic        sfifo_quar1_pop;
  logic        sfifo_quar1_clr;
  logic [31:0] sfifo_quar1_wdata;
  logic [31:0] sfifo_quar1_rdata;
  logic        sfifo_quar1_not_full;
  logic        sfifo_quar1_not_empty;
  logic        sfifo_quar1_err;

  logic        sfifo_essw_push;
  logic        sfifo_essw_pop;
  logic        sfifo_essw_clr;
  logic [31:0] sfifo_essw_wdata;
  logic [31:0] sfifo_essw_rdata;
  logic [2:0 ] sfifo_essw_depth;
  logic        sfifo_essw_not_full;
  logic        sfifo_essw_not_empty;
  logic        sfifo_essw_err;

  logic        sfifo_eshw_push;
  logic        sfifo_eshw_pop;
  logic        sfifo_eshw_clr;
  logic [31:0] sfifo_eshw_wdata;
  logic [31:0] sfifo_eshw_rdata;
  logic [2:0]  sfifo_eshw_depth;
  logic        sfifo_eshw_not_full;
  logic        sfifo_eshw_not_empty;
  logic        sfifo_eshw_err;

  logic              es_src_fifo_pop;
  logic              afifo_esana_not_empty;
  logic              afifo_esana_pop;
  logic              afifo_esana_err;
  logic [7:0]        afifo_esana_rdata;
  logic [2:0]        afifo_esana_depth;
  logic [7:0]        mg_bits_err_50mhz;
  logic              es_ana_en_50mhz;
  logic              ana_fifo_wr_err_50mhz;
  logic              es_ana_fifo_rdy_50mhz;
  logic              sel_ana_src;
  logic              rct_test_active;
  logic [15:0]       rct_max_cnt;
  logic              rct_samples_match;
  logic              rct_test_fail;
  logic              apt_test_active;
  logic              apt_reset_test;
  logic              apt_samples_match;
  logic              apt_test_fail;
  logic [15:0]       apt_max_cnt;
  logic [15:0]       apt_window;
  logic              es_health_fail;
  logic              es_load_byte0;
  logic              es_load_byte1;
  logic              es_load_byte2;
  logic              es_load_byte3;
  logic              dwstr_fifo_push;
  logic              dwstr_fifo_swap;
  logic              dwstr_fifo_clr;
  logic              dwstr_fifo_not_full;
  logic              other_dwstr_fifo_empty;
  logic [31:0]       quar_rdata;
  logic              quar_not_empty;
  logic              quar_pop;
  logic              push_to_sw_regs;

  // flops
  logic        entropy_val_q, entropy_val_d;
  logic [15:0] es_rate_cntr_q, es_rate_cntr_d;
  logic [7:0]  rct_prev_sample_q, rct_prev_sample_d;
  logic [15:0] rct_rep_cntr_q, rct_rep_cntr_d;
  logic [7:0]  apt_initial_sample_q, apt_initial_sample_d;
  logic [15:0] apt_sample_cntr_q, apt_sample_cntr_d;
  logic [15:0] apt_match_cntr_q, apt_match_cntr_d;
  logic [31:0] entr_byte_align_q, entr_byte_align_d;
  logic        swap_ptr_q, swap_ptr_d;

  always_ff @(posedge clk_i or negedge rst_ni)
    if (!rst_ni) begin
      entropy_val_q         <= '0;
      es_rate_cntr_q        <= 16'h0001;
      rct_prev_sample_q     <= '0;
      rct_rep_cntr_q        <= '0;
      apt_initial_sample_q  <= '0;
      apt_sample_cntr_q     <= '0;
      apt_match_cntr_q      <= '0;
      entr_byte_align_q     <= '0;
      swap_ptr_q            <= '0;
    end else begin
      entropy_val_q         <= entropy_val_d;
      es_rate_cntr_q        <= es_rate_cntr_d;
      rct_prev_sample_q     <= rct_prev_sample_d;
      rct_rep_cntr_q        <= rct_rep_cntr_d;
      apt_initial_sample_q  <= apt_initial_sample_d;
      apt_sample_cntr_q     <= apt_sample_cntr_d;
      apt_match_cntr_q      <= apt_match_cntr_d;
      entr_byte_align_q     <= entr_byte_align_d;
      swap_ptr_q            <= swap_ptr_d;
    end

  assign es_enable = (|reg2hw.es_conf.enable.q);
  assign es_enable_dig = reg2hw.es_conf.enable.q[0];
  assign es_enable_ana = reg2hw.es_conf.enable.q[1];
  assign load_seed = ~es_enable;

  assign es_mg_enable_o = reg2hw.es_conf.ana_src_en.q;

  // 50Mhz time domain flops
  logic  bits_err_50mhz_q,  bits_err_50mhz_d;
  logic  fifo_err_50mhz_q,  fifo_err_50mhz_d;

  always_ff @(posedge clk_es_50mhz_i or negedge rst_es_50mhz_ni)
    if (!rst_es_50mhz_ni) begin
      bits_err_50mhz_q      <= '0;
      fifo_err_50mhz_q      <= '0;
    end else begin
      bits_err_50mhz_q      <= bits_err_50mhz_d;
      fifo_err_50mhz_q      <= fifo_err_50mhz_d;
    end

  //--------------------------------------------
  // instantiate interrupt hardware primitives
  //--------------------------------------------

  prim_intr_hw #(.Width(1)) intr_hw_es_entropy_valid (
    .event_intr_i           (event_es_entropy_valid),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.es_entropy_valid.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.es_entropy_valid.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.es_entropy_valid.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.es_entropy_valid.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.es_entropy_valid.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.es_entropy_valid.d),
    .intr_o                 (es_entropy_valid_o)
  );

  prim_intr_hw #(.Width(1)) intr_hw_es_ana_src_ok (
    .event_intr_i           (event_es_ana_src_ok),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.es_ana_src_ok.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.es_ana_src_ok.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.es_ana_src_ok.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.es_ana_src_ok.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.es_ana_src_ok.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.es_ana_src_ok.d),
    .intr_o                 (es_ana_src_ok_o)
  );

  prim_intr_hw #(.Width(1)) intr_hw_es_ana_bits_err (
    .event_intr_i           (event_es_ana_bits_err),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.es_ana_bits_err.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.es_ana_bits_err.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.es_ana_bits_err.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.es_ana_bits_err.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.es_ana_bits_err.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.es_ana_bits_err.d),
    .intr_o                 (es_ana_bits_err_o)
  );

  prim_intr_hw #(.Width(1)) intr_hw_es_ana_fifo_err (
    .event_intr_i           (event_es_ana_fifo_err),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.es_ana_fifo_err.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.es_ana_fifo_err.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.es_ana_fifo_err.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.es_ana_fifo_err.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.es_ana_fifo_err.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.es_ana_fifo_err.d),
    .intr_o                 (es_ana_fifo_err_o)
  );

  prim_intr_hw #(.Width(1)) intr_hw_es_fifo_err (
    .event_intr_i           (event_es_fifo_err),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.es_fifo_err.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.es_fifo_err.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.es_fifo_err.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.es_fifo_err.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.es_fifo_err.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.es_fifo_err.d),
    .intr_o                 (es_fifo_err_o)
  );

  //--------------------------------------------
  // lfsr - a version of a entropy source
  //--------------------------------------------

  assign lfsr_enable = es_enable_dig && es_rate_entropy_valid;

  prim_lfsr #(.LfsrDw(8), .EntropyDw(8), .StateOutDw(8), .DefaultSeed(1), .CustomCoeffs('0))
    u_prim_lfsr (
    .clk_i          (clk_i),
    .rst_ni         (rst_ni),
    .seed_en_i      (load_seed),
    .seed_i         (seed_value),
    .lfsr_en_i      (lfsr_enable),
    .entropy_i      ('0),
    .state_o        (lfsr_value)
  );

  // entropy rate limiter

  assign es_rate_cntr_d = ~es_enable ? 16'h0001 :
         (es_rate == '0) ? 16'h0000 :
         es_rate_entropy_valid ? es_rate :
         (es_rate_cntr_q - 1);

  assign es_rate_entropy_valid =
         ~es_enable ? 1'b0 :
         (es_rate == '0) ? 1'b0 :
         (es_rate_cntr_q == 16'h0001);

  //--------------------------------------------
  // tlul register settings
  //--------------------------------------------


  // seed register
  assign seed_value = reg2hw.es_seed.q;

  // es rate register
  assign es_rate = reg2hw.es_rate.q;

  // es fifo threshold register
  assign es_reg_fifo_thresh = reg2hw.es_thresh.q;

  // set the interrupt event when enabled
  assign event_es_entropy_valid = entropy_val_q;

  // set the interrupt sources
  assign event_es_fifo_err =
         afifo_esana_err |
         sfifo_esdig_err |
         sfifo_quar0_err |
         sfifo_quar1_err |
         sfifo_essw_err |
         sfifo_eshw_err;

  // set the debug status reg
  assign hw2reg.es_status.fifo0_depth.d = afifo_esana_depth;
  assign hw2reg.es_status.fifo1_depth.d = sfifo_esdig_depth;
  assign hw2reg.es_status.fifo2_depth.d = sfifo_essw_depth;
  assign hw2reg.es_status.fifo3_depth.d = sfifo_eshw_depth;


  //--------------------------------------------
  // async FIFO for analog bus input
  //--------------------------------------------

  prim_flop_2sync
    #(.Width(1)
      ) u_prim_flop_2sync_ana_src_ok
      (
       .clk_i  (clk_i),
       .rst_ni (rst_ni),
       .d      (mg_es_ok_i), // 50 mhz domain
       .q      (event_es_ana_src_ok)
       );

  // bits_err

  always_comb begin : mg_bits_chk
    for (int i = 0; i < 8; i++) begin
      mg_bits_err_50mhz[i] = (mg_bits_p_i[i] == mg_bits_n_i[i]);
    end
  end

  assign bits_err_50mhz_d = ~es_ana_en_50mhz ? 1'b0 :
                            |mg_bits_err_50mhz ? 1'b1 :
                            bits_err_50mhz_q;
  prim_flop_2sync
    #(.Width(1)
      ) u_prim_flop_2sync_bits_err
      (
       .clk_i  (clk_i),
       .rst_ni (rst_ni),
       .d      (bits_err_50mhz_q),
       .q      (event_es_ana_bits_err)
       );


  // fifo_err

  assign ana_fifo_wr_err_50mhz = es_ana_en_50mhz & ~es_ana_fifo_rdy_50mhz;

  assign fifo_err_50mhz_d = ~es_ana_en_50mhz ? 1'b0 :
                            ana_fifo_wr_err_50mhz ? 1'b1 :
                            fifo_err_50mhz_q;
  prim_flop_2sync
    #(.Width(1)
      ) u_prim_flop_2sync_fifo_err
      (
       .clk_i  (clk_i),
       .rst_ni (rst_ni),
       .d      (fifo_err_50mhz_q),
       .q      (event_es_ana_fifo_err)
       );

  prim_flop_2sync
    #(.Width(1)
      ) u_prim_flop_2sync_cfg
      (
       .clk_i  (clk_es_50mhz_i),
       .rst_ni (rst_es_50mhz_ni),
       .d      (es_enable_ana),
       .q      (es_ana_en_50mhz)
       );

  prim_fifo_async #(
    .Width(AnFifoWidth),
    .Depth(AnFifoDepth)
  ) usbdev_avfifo (
    .clk_wr_i  (clk_es_50mhz_i),
    .rst_wr_ni (rst_es_50mhz_ni),

    .wvalid    (es_ana_en_50mhz), // push
    .wready    (es_ana_fifo_rdy_50mhz),
    .wdata     (mg_bits_p_i),
    .wdepth    (),

    .clk_rd_i  (clk_i),
    .rst_rd_ni (rst_ni),
    .rvalid    (afifo_esana_not_empty),
    .rready    (afifo_esana_pop),      // pop
    .rdata     (afifo_esana_rdata),
    .rdepth    (afifo_esana_depth)
  );

  assign afifo_esana_pop = es_enable_ana && es_src_fifo_pop;

  // fifo err
  assign afifo_esana_err =
         (afifo_esana_pop & ~afifo_esana_not_empty );



  prim_fifo_sync # (.Width(8),.Pass(0),.Depth(4))
    u_prim_fifo_sync_esdig (
    .clk_i          (clk_i),
    .rst_ni         (rst_ni),
    .clr_i          (sfifo_esdig_clr),
    .wvalid         (sfifo_esdig_push),
    .wready         (sfifo_esdig_not_full),
    .wdata          (sfifo_esdig_wdata),
    .rvalid         (sfifo_esdig_not_empty),
    .rready         (sfifo_esdig_pop),
    .rdata          (sfifo_esdig_rdata),
    .depth          (sfifo_esdig_depth)
  );

  // fifo controls
  assign sfifo_esdig_push = es_enable & es_rate_entropy_valid & sfifo_esdig_not_full;
  assign sfifo_esdig_clr  = ~es_enable;
  assign sfifo_esdig_wdata = lfsr_value;
  assign sfifo_esdig_pop = es_enable_dig && es_src_fifo_pop;

  // note: allow input lfsr entropy to drop

  // fifo err
  assign sfifo_esdig_err =
         (sfifo_esdig_pop & ~sfifo_esdig_not_empty );


  //--------------------------------------------
  // health tests
  //--------------------------------------------

  assign sel_ana_src = es_enable_ana;

  assign es_entropy_bits_vld = sel_ana_src ? afifo_esana_not_empty : sfifo_esdig_not_empty;

  assign es_entropy_bits = (sel_ana_src ? afifo_esana_rdata : sfifo_esdig_rdata); 


  // Repetition Count Test (RCT)
  //
  // Point of test
  //  check for back to back patterns up to a
  //  limit, fail if it does

  assign rct_test_active = reg2hw.es_conf.rct_en.q;
  assign rct_max_cnt = reg2hw.es_rct_health.q;

  // NIST A sample
  assign rct_prev_sample_d = rct_test_active ? 8'b0 :
         es_entropy_bits_vld ? es_entropy_bits :
         rct_prev_sample_q;

  assign rct_samples_match = (rct_prev_sample_q == es_entropy_bits);

  // NIST B counter
  assign rct_rep_cntr_d = ~rct_test_active ? 16'h0001 :
         (es_entropy_bits_vld & rct_samples_match) ? (rct_rep_cntr_q+1) :
         16'h0001;

  assign rct_test_fail = rct_test_active & (rct_rep_cntr_q >= rct_max_cnt);


  // Adaptive Proportion Test (APT)
  //
  // Point of test
  //  sample once, then check for period of time if
  //  that pattern appears again, fail if it does

  assign apt_test_active = reg2hw.es_conf.apt_en.q;
  assign apt_max_cnt = reg2hw.es_apt_health.apt_max.q;
  assign apt_window  = reg2hw.es_apt_health.apt_win.q;

  // NIST N value
  assign apt_reset_test = ~apt_test_active | (apt_sample_cntr_q >= apt_window);

  // NIST A counter
  assign apt_initial_sample_d =
         (apt_reset_test & es_entropy_bits_vld) ? es_entropy_bits :
         apt_initial_sample_q;

  // NIST S counter
  assign apt_sample_cntr_d = apt_reset_test ? 16'b0 :
         es_entropy_bits_vld ? (apt_sample_cntr_q+1) :
         apt_sample_cntr_q;

  assign apt_samples_match = es_entropy_bits_vld & (apt_initial_sample_q == es_entropy_bits);

  // NIST B counter
  assign apt_match_cntr_d = apt_reset_test ? 16'b0 :
         (es_entropy_bits_vld & apt_samples_match) ? (apt_match_cntr_q+1) :
         apt_match_cntr_q;

  assign apt_test_fail = apt_test_active & (apt_match_cntr_q >= apt_max_cnt);


  assign es_health_fail = rct_test_fail | apt_test_fail;


  //--------------------------------------------
  // align entropy bits and load FIFOs
  //--------------------------------------------

  assign es_src_fifo_pop = (es_load_byte0 |
                            es_load_byte1 |
                            es_load_byte2 |
                            es_load_byte3);

  assign entr_byte_align_d =
         es_load_byte0 ? {entr_byte_align_q[31:8],es_entropy_bits} :
         es_load_byte1 ? {entr_byte_align_q[31:16],es_entropy_bits,entr_byte_align_q[7:0]} :
         es_load_byte2 ? {entr_byte_align_q[31:24],es_entropy_bits,entr_byte_align_q[15:0]} :
         es_load_byte3 ? {es_entropy_bits,entr_byte_align_q[23:0]} :
         entr_byte_align_q;


  entropy_src_align_sm
    u_entropy_src_align_sm
      (
       .clk_i(clk_i),
       .rst_ni(rst_ni),
       .es_enable_i(es_enable),
       .es_health_fail_i(es_health_fail),
       .upstr_fifo_vld_i(es_entropy_bits_vld),
       .dwstr_fifo_not_full_i(dwstr_fifo_not_full),
       .dwstr_fifo_push_o(dwstr_fifo_push),
       .es_load_byte0_o(es_load_byte0),
       .es_load_byte1_o(es_load_byte1),
       .es_load_byte2_o(es_load_byte2),
       .es_load_byte3_o(es_load_byte3),
       .other_dwstr_fifo_empty_i(other_dwstr_fifo_empty),
       .dwstr_fifo_swap_o(dwstr_fifo_swap),
       .dwstr_fifo_clr_o(dwstr_fifo_clr)
       );


  //--------------------------------------------
  // fifos for entropy quarantine
  //--------------------------------------------

  assign swap_ptr_d = dwstr_fifo_swap ? ~swap_ptr_q : swap_ptr_q;

  assign dwstr_fifo_not_full = swap_ptr_q ? sfifo_quar1_not_full : sfifo_quar0_not_full;
  assign other_dwstr_fifo_empty = swap_ptr_q ? ~sfifo_quar0_not_empty : ~sfifo_quar1_not_empty;

  prim_fifo_sync # (.Width(32),.Pass(0),.Depth(EsFifoDepth))
    u_prim_fifo_sync_quar0 (
    .clk_i          (clk_i),
    .rst_ni         (rst_ni),
    .clr_i          (sfifo_quar0_clr),
    .wvalid         (sfifo_quar0_push),
    .wready         (sfifo_quar0_not_full),
    .wdata          (sfifo_quar0_wdata),
    .rvalid         (sfifo_quar0_not_empty),
    .rready         (sfifo_quar0_pop),
    .rdata          (sfifo_quar0_rdata),
    .depth          ()
  );

  // fifo controls
  assign sfifo_quar0_push = es_enable & dwstr_fifo_push & ~swap_ptr_q;
  assign sfifo_quar0_clr  = es_enable & dwstr_fifo_clr  & ~swap_ptr_q;
  assign sfifo_quar0_wdata = entr_byte_align_q;
  assign sfifo_quar0_pop = es_enable & quar_pop & swap_ptr_q;

  // fifo err
  assign sfifo_quar0_err =
         (sfifo_quar0_push & ~sfifo_quar0_not_full) |
         (sfifo_quar0_pop & ~sfifo_quar0_not_empty );



  prim_fifo_sync # (.Width(32),.Pass(0),.Depth(EsFifoDepth))
    u_prim_fifo_sync_quar1 (
    .clk_i          (clk_i),
    .rst_ni         (rst_ni),
    .clr_i          (sfifo_quar1_clr),
    .wvalid         (sfifo_quar1_push),
    .wready         (sfifo_quar1_not_full),
    .wdata          (sfifo_quar1_wdata),
    .rvalid         (sfifo_quar1_not_empty),
    .rready         (sfifo_quar1_pop),
    .rdata          (sfifo_quar1_rdata),
    .depth          ()
  );

  // fifo controls
  assign sfifo_quar1_push = es_enable & dwstr_fifo_push & swap_ptr_q;
  assign sfifo_quar1_clr  = es_enable & dwstr_fifo_clr  & swap_ptr_q;
  assign sfifo_quar1_wdata = entr_byte_align_q;
  assign sfifo_quar1_pop =  es_enable & quar_pop & ~swap_ptr_q;

  // fifo err
  assign sfifo_quar1_err =
         (sfifo_quar1_push & ~sfifo_quar1_not_full) |
         (sfifo_quar1_pop & ~sfifo_quar1_not_empty );



  //--------------------------------------------
  // fifos for final distribution
  //--------------------------------------------

  assign push_to_sw_regs = efuse_cs_sw_reg_en_i && sfifo_essw_not_full;

  assign quar_rdata = ~swap_ptr_q ? sfifo_quar1_rdata : sfifo_quar0_rdata;
  assign quar_not_empty = ~swap_ptr_q ? sfifo_quar1_not_empty : sfifo_quar0_not_empty;
  assign quar_pop = (sfifo_essw_not_full | sfifo_eshw_not_full) & quar_not_empty;


  // this fifo feeds the sw register interface

  prim_fifo_sync # (.Width(32),.Pass(0),.Depth(4))
    u_prim_fifo_sync_essw (
    .clk_i          (clk_i),
    .rst_ni         (rst_ni),
    .clr_i          (sfifo_essw_clr),
    .wvalid         (sfifo_essw_push),
    .wready         (sfifo_essw_not_full),
    .wdata          (sfifo_essw_wdata),
    .rvalid         (sfifo_essw_not_empty),
    .rready         (sfifo_essw_pop),
    .rdata          (sfifo_essw_rdata),
    .depth          (sfifo_essw_depth)
  );

  // fifo controls
  assign sfifo_essw_push = es_enable & quar_not_empty & push_to_sw_regs;
  assign sfifo_essw_clr  = ~es_enable;
  assign sfifo_essw_wdata = quar_rdata;
  assign sfifo_essw_pop = es_enable & esentropy_rd_pls & efuse_cs_sw_reg_en_i;

  // fifo err
  assign sfifo_essw_err =
         (sfifo_essw_push & ~sfifo_essw_not_full) |
         (sfifo_essw_pop & ~sfifo_essw_not_empty );

  // set the es entropy to the read reg
  assign hw2reg.es_entropy.d = sfifo_essw_rdata;
  assign esentropy_rd_pls = reg2hw.es_entropy.re;

  // threshold
  assign es_fifo_thresh = es_reg_fifo_thresh[2:0];

  // entropy valid
  assign entropy_val_d = ~es_enable ? 1'b0 : (sfifo_essw_depth >= es_fifo_thresh);

  // set the es fifo depth to the read reg
  assign hw2reg.es_fdepthst.d = sfifo_essw_depth;



  // this fifo feeds the hw bus interface

  prim_fifo_sync # (.Width(32),.Pass(0),.Depth(4))
    u_prim_fifo_sync_eshw (
    .clk_i          (clk_i),
    .rst_ni         (rst_ni),
    .clr_i          (sfifo_eshw_clr),
    .wvalid         (sfifo_eshw_push),
    .wready         (sfifo_eshw_not_full),
    .wdata          (sfifo_eshw_wdata),
    .rvalid         (sfifo_eshw_not_empty),
    .rready         (sfifo_eshw_pop),
    .rdata          (sfifo_eshw_rdata),
    .depth          (sfifo_eshw_depth)
  );

  // fifo controls
  assign sfifo_eshw_push = es_enable & quar_not_empty & ~push_to_sw_regs;
  assign sfifo_eshw_clr  = ~es_enable;
  assign sfifo_eshw_wdata = quar_rdata;
  assign sfifo_eshw_pop = es_enable & entropy_src_hw_if_i.entropy_src_rdy;

  // fifo err
  assign sfifo_eshw_err =
         (sfifo_eshw_push & ~sfifo_eshw_not_full) |
         (sfifo_eshw_pop & ~sfifo_eshw_not_empty );

  // drive out hw interface
  assign entropy_src_hw_if_o.entropy_src_vld = sfifo_eshw_not_empty;
  assign entropy_src_hw_if_o.entropy_src_bits = sfifo_eshw_rdata;

  //--------------------------------------------
  // diag settings
  //--------------------------------------------

  assign hw2reg.es_status.diag.d  =
         reg2hw.es_regen.q &
         (&reg2hw.es_entropy.q);

endmodule
