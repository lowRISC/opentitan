// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: entropy_src core module
//

module entropy_src_core
import entropy_src_pkg::*;
#(
    parameter int unsigned EsFifoDepth = 16
) (
    input clk_i,
    input rst_ni,

    input  entropy_src_reg_pkg::entropy_src_reg2hw_t reg2hw,
    output entropy_src_reg_pkg::entropy_src_hw2reg_t hw2reg,

    // Efuse Interface
    input efuse_es_sw_reg_en_i,


    // Entropy Interface
    input  entropy_src_hw_if_req_t entropy_src_hw_if_i,
    output entropy_src_hw_if_rsp_t entropy_src_hw_if_o,

    // RNG Interface
    output entropy_src_rng_req_t entropy_src_rng_o,
    input  entropy_src_rng_rsp_t entropy_src_rng_i,

    output logic es_entropy_valid_o,
    output logic es_rct_failed_o,
    output logic es_apt_failed_o,
    output logic es_fifo_err_o
);

  import entropy_src_reg_pkg::*;

  localparam int unsigned PostHTDepth = $clog2(EsFifoDepth);
  localparam int unsigned RngBusWidth = 4;

  // signals
  logic [RngBusWidth-1:0] lfsr_value;
  logic [RngBusWidth-1:0] seed_value;
  logic load_seed;
  logic es_enable;
  logic es_enable_dig;
  logic es_enable_rng;
  logic rng_bit_en;
  logic [1:0] rng_bit_sel;
  logic lfsr_enable;
  logic esentropy_rd_pls;
  logic event_es_entropy_valid;
  logic event_es_apt_failed;
  logic event_es_rct_failed;
  //  logic       event_es_rng_bits_err;
  logic event_es_fifo_err;
  logic [15:0] es_rate;
  logic es_rate_entropy_valid;
  logic es_rate_entropy_valid_en;
  logic [2:0] es_fifo_thresh;
  logic es_rng_src_ok;

  logic sfifo_esdig_push;
  logic sfifo_esdig_pop;
  logic sfifo_esdig_clr;
  logic [RngBusWidth-1:0] sfifo_esdig_wdata;
  logic [RngBusWidth-1:0] sfifo_esdig_rdata;
  logic [2:0] sfifo_esdig_depth;
  logic sfifo_esdig_not_full;
  logic sfifo_esdig_not_empty;
  logic sfifo_esdig_err;

  logic sfifo_postht_push;
  logic sfifo_postht_pop;
  logic sfifo_postht_clr;
  logic [31:0] sfifo_postht_wdata;
  logic [31:0] sfifo_postht_rdata;
  logic [PostHTDepth:0] sfifo_postht_depth;
  logic sfifo_postht_not_full;
  logic sfifo_postht_not_empty;
  logic sfifo_postht_err;
  logic sfifo_postht_avail;

  logic sfifo_essw_push;
  logic sfifo_essw_pop;
  logic sfifo_essw_clr;
  logic [31:0] sfifo_essw_wdata;
  logic [31:0] sfifo_essw_rdata;
  logic [2:0] sfifo_essw_depth;
  logic sfifo_essw_not_full;
  logic sfifo_essw_not_empty;
  logic sfifo_essw_err;

  logic sfifo_eshw_push;
  logic sfifo_eshw_pop;
  logic sfifo_eshw_clr;
  logic [31:0] sfifo_eshw_wdata;
  logic [31:0] sfifo_eshw_rdata;
  logic [2:0] sfifo_eshw_depth;
  logic sfifo_eshw_not_full;
  logic sfifo_eshw_not_empty;
  logic sfifo_eshw_err;

  //  logic [RngBusWidth-1:0] rng_bits_err;
  logic [RngBusWidth-1:0] rct_active;
  logic [15:0] rct_max_cnt;
  logic [RngBusWidth-1:0] apt_active;
  logic [15:0] apt_max_cnt;
  logic [15:0] apt_window;
  logic [RngBusWidth-1:0] apt_fail_pls;
  logic [RngBusWidth-1:0] rct_fail_pls;
  logic [RngBusWidth-1:0] shtests_passing;
  logic [RngBusWidth-1:0] packer_esbus_wdata;
  logic [31:0] packer_esbus_rdata;
  logic packer_esbus_push;
  logic packer_esbus_clr;
  logic packer_esbus_valid;
  logic packer_esbit_wdata;
  logic [31:0] packer_esbit_rdata;
  logic packer_esbit_push;
  logic packer_esbit_clr;
  logic packer_esbit_valid;
  logic packer_valid;
  logic fill_sfifo_essw;

  // flops
  logic entropy_val_q, entropy_val_d;
  logic [15:0] es_rate_cntr_q, es_rate_cntr_d;
  //  logic        rng_bits_err_q, rng_bits_err_d;

  always_ff @(posedge clk_i or negedge rst_ni)
    if (!rst_ni) begin
      entropy_val_q <= '0;
      es_rate_cntr_q <= 16'h0001;
      //      rng_bits_err_q        <= '0;
    end else begin
      entropy_val_q <= entropy_val_d;
      es_rate_cntr_q <= es_rate_cntr_d;
      //      rng_bits_err_q        <= rng_bits_err_d;
    end

  assign es_enable = (|reg2hw.es_conf.enable.q);
  assign es_enable_dig = reg2hw.es_conf.enable.q[0];
  assign es_enable_rng = reg2hw.es_conf.enable.q[1];
  assign load_seed = ~es_enable;

  assign entropy_src_rng_o.rng_enable = reg2hw.es_conf.rng_src_en.q;


  //--------------------------------------------
  // instantiate interrupt hardware primitives
  //--------------------------------------------

  prim_intr_hw #(
      .Width(1)
  ) intr_hw_es_entropy_valid (
      .event_intr_i          (event_es_entropy_valid),
      .reg2hw_intr_enable_q_i(reg2hw.intr_enable.es_entropy_valid.q),
      .reg2hw_intr_test_q_i  (reg2hw.intr_test.es_entropy_valid.q),
      .reg2hw_intr_test_qe_i (reg2hw.intr_test.es_entropy_valid.qe),
      .reg2hw_intr_state_q_i (reg2hw.intr_state.es_entropy_valid.q),
      .hw2reg_intr_state_de_o(hw2reg.intr_state.es_entropy_valid.de),
      .hw2reg_intr_state_d_o (hw2reg.intr_state.es_entropy_valid.d),
      .intr_o                (es_entropy_valid_o)
  );

  prim_intr_hw #(
      .Width(1)
  ) intr_hw_es_rct_failed (
      .event_intr_i          (event_es_rct_failed),
      .reg2hw_intr_enable_q_i(reg2hw.intr_enable.es_rct_failed.q),
      .reg2hw_intr_test_q_i  (reg2hw.intr_test.es_rct_failed.q),
      .reg2hw_intr_test_qe_i (reg2hw.intr_test.es_rct_failed.qe),
      .reg2hw_intr_state_q_i (reg2hw.intr_state.es_rct_failed.q),
      .hw2reg_intr_state_de_o(hw2reg.intr_state.es_rct_failed.de),
      .hw2reg_intr_state_d_o (hw2reg.intr_state.es_rct_failed.d),
      .intr_o                (es_rct_failed_o)
  );

  prim_intr_hw #(
      .Width(1)
  ) intr_hw_es_apt_failed (
      .event_intr_i          (event_es_apt_failed),
      .reg2hw_intr_enable_q_i(reg2hw.intr_enable.es_apt_failed.q),
      .reg2hw_intr_test_q_i  (reg2hw.intr_test.es_apt_failed.q),
      .reg2hw_intr_test_qe_i (reg2hw.intr_test.es_apt_failed.qe),
      .reg2hw_intr_state_q_i (reg2hw.intr_state.es_apt_failed.q),
      .hw2reg_intr_state_de_o(hw2reg.intr_state.es_apt_failed.de),
      .hw2reg_intr_state_d_o (hw2reg.intr_state.es_apt_failed.d),
      .intr_o                (es_apt_failed_o)
  );


  prim_intr_hw #(
      .Width(1)
  ) intr_hw_es_fifo_err (
      .event_intr_i          (event_es_fifo_err),
      .reg2hw_intr_enable_q_i(reg2hw.intr_enable.es_fifo_err.q),
      .reg2hw_intr_test_q_i  (reg2hw.intr_test.es_fifo_err.q),
      .reg2hw_intr_test_qe_i (reg2hw.intr_test.es_fifo_err.qe),
      .reg2hw_intr_state_q_i (reg2hw.intr_state.es_fifo_err.q),
      .hw2reg_intr_state_de_o(hw2reg.intr_state.es_fifo_err.de),
      .hw2reg_intr_state_d_o (hw2reg.intr_state.es_fifo_err.d),
      .intr_o                (es_fifo_err_o)
  );

  //--------------------------------------------
  // lfsr - a version of a entropy source
  //--------------------------------------------

  assign lfsr_enable = es_enable_dig && es_rate_entropy_valid;

  prim_lfsr #(
      .LfsrDw(RngBusWidth),
      .EntropyDw(RngBusWidth),
      .StateOutDw(RngBusWidth),
      .DefaultSeed(1),
      .CustomCoeffs('0)
  ) u_prim_lfsr (
      .clk_i    (clk_i),
      .rst_ni   (rst_ni),
      .seed_en_i(load_seed),
      .seed_i   (seed_value),
      .lfsr_en_i(lfsr_enable),
      .entropy_i('0),
      .state_o  (lfsr_value)
  );

  // entropy rate limiter

  assign es_rate_cntr_d = ~es_rate_entropy_valid_en ? 16'h0001 : (es_rate == '0) ? 16'h0000 :
      es_rate_entropy_valid ? es_rate : (es_rate_cntr_q - 1);

  assign es_rate_entropy_valid =
      ~es_rate_entropy_valid_en ? 1'b0 : (es_rate == '0) ? 1'b0 : (es_rate_cntr_q == 16'h0001);

  assign es_rate_entropy_valid_en = (es_enable_rng & es_rng_src_ok) | es_enable_dig;

  //--------------------------------------------
  // tlul register settings
  //--------------------------------------------


  // seed register
  assign seed_value = reg2hw.es_seed.q;

  // es rate register
  assign es_rate = reg2hw.es_rate.q;

  // set the interrupt event when enabled
  assign event_es_entropy_valid = entropy_val_q;

  // set the interrupt sources
  assign event_es_fifo_err = sfifo_esdig_err | sfifo_postht_err | sfifo_essw_err | sfifo_eshw_err;

  // set the debug status reg
  assign hw2reg.es_fifo_status.dig_src_depth.d = sfifo_esdig_depth;
  assign hw2reg.es_fifo_status.hwif_depth.d = sfifo_eshw_depth;
  assign hw2reg.es_fifo_status.es_depth.d = sfifo_postht_depth;


  //--------------------------------------------
  // basic checks for RNG bus input
  //--------------------------------------------

  assign rng_bit_en = reg2hw.es_conf.rng_bit_en.q;
  assign rng_bit_sel = reg2hw.es_conf.rng_bit_sel.q;


  assign es_rng_src_ok = entropy_src_rng_i.rng_ok;


  prim_fifo_sync #(
      .Width(RngBusWidth),
      .Pass(0),
      .Depth(4)
  ) u_prim_fifo_sync_esdig (
      .clk_i   (clk_i),
      .rst_ni  (rst_ni),
      .clr_i   (sfifo_esdig_clr),
      .wvalid_i(sfifo_esdig_push),
      .wready_o(sfifo_esdig_not_full),
      .wdata_i (sfifo_esdig_wdata),
      .rvalid_o(sfifo_esdig_not_empty),
      .rready_i(sfifo_esdig_pop),
      .rdata_o (sfifo_esdig_rdata),
      .depth_o (sfifo_esdig_depth)
  );

  // fifo controls
  assign sfifo_esdig_push = es_enable & es_rate_entropy_valid & sfifo_esdig_not_full;
  assign sfifo_esdig_clr = ~es_enable;
  assign sfifo_esdig_wdata = es_enable_dig ? lfsr_value : entropy_src_rng_i.rng_b;
  assign sfifo_esdig_pop = es_enable & sfifo_esdig_not_empty & sfifo_postht_avail;

  // note: allow input lfsr entropy to drop

  // fifo err
  assign sfifo_esdig_err = (sfifo_esdig_pop & ~sfifo_esdig_not_empty);

  // pack esbus before moving to a 32 bit bus

  prim_packer #(
      .InW(RngBusWidth),
      .OutW(32)
  ) u_prim_packer_esbus (
      .clk_i       (clk_i),
      .rst_ni      (rst_ni),
      .valid_i     (packer_esbus_push),
      .data_i      (packer_esbus_wdata),
      .mask_i      ({RngBusWidth{1'b1}}),
      .ready_o     (),
      .valid_o     (packer_esbus_valid),
      .data_o      (packer_esbus_rdata),
      .mask_o      (),
      .ready_i     (1'b1),
      .flush_i     (packer_esbus_clr),
      .flush_done_o()
  );

  assign packer_esbus_push = ~rng_bit_en & sfifo_esdig_pop;
  assign packer_esbus_wdata = sfifo_esdig_rdata;
  assign packer_esbus_clr = ~es_enable;

  // pack esbit before moving to a 32 bit bus

  prim_packer #(
      .InW(1),
      .OutW(32)
  ) u_prim_packer_esbit (
      .clk_i       (clk_i),
      .rst_ni      (rst_ni),
      .valid_i     (packer_esbit_push),
      .data_i      (packer_esbit_wdata),
      .mask_i      (1'b1),
      .ready_o     (),
      .valid_o     (packer_esbit_valid),
      .data_o      (packer_esbit_rdata),
      .mask_o      (),
      .ready_i     (1'b1),
      .flush_i     (packer_esbit_clr),
      .flush_done_o()
  );

  assign packer_esbit_push = rng_bit_en & sfifo_esdig_pop;
  assign packer_esbit_clr = ~es_enable;
  assign packer_esbit_wdata = (rng_bit_sel == 2'h0) ? sfifo_esdig_rdata[0] : (rng_bit_sel == 2'h1) ?
      sfifo_esdig_rdata[1] : (rng_bit_sel == 2'h2) ? sfifo_esdig_rdata[2] : sfifo_esdig_rdata[3];


  // combine packers
  assign packer_valid = packer_esbus_valid | packer_esbit_valid;


  prim_fifo_sync #(
      .Width(32),
      .Pass(0),
      .Depth(EsFifoDepth)
  ) u_prim_fifo_sync_postht (
      .clk_i   (clk_i),
      .rst_ni  (rst_ni),
      .clr_i   (sfifo_postht_clr),
      .wvalid_i(sfifo_postht_push),
      .wready_o(sfifo_postht_not_full),
      .wdata_i (sfifo_postht_wdata),
      .rvalid_o(sfifo_postht_not_empty),
      .rready_i(sfifo_postht_pop),
      .rdata_o (sfifo_postht_rdata),
      .depth_o (sfifo_postht_depth)
  );

  // fifo controls
  assign sfifo_postht_push = es_enable & packer_valid & (&shtests_passing);
  assign sfifo_postht_clr = ~es_enable;
  assign sfifo_postht_wdata = rng_bit_en ? packer_esbit_rdata : packer_esbus_rdata;
  assign sfifo_postht_pop =
      es_enable & sfifo_postht_not_empty & (fill_sfifo_essw | sfifo_eshw_not_full);

  // allow one extra location because of packer
  assign sfifo_postht_avail = (sfifo_postht_depth < (EsFifoDepth - 1));

  // fifo err
  assign sfifo_postht_err =
      (sfifo_postht_push & ~sfifo_postht_not_full) | (sfifo_postht_pop & ~sfifo_postht_not_empty);


  //--------------------------------------------
  // health tests
  //--------------------------------------------

  genvar ta;
  generate
    for (ta = 0; ta < RngBusWidth; ta = ta + 1) begin : gen_test_act
      assign rct_active[ta] =
          rng_bit_en ? ((rng_bit_sel == ta) & reg2hw.es_conf.rct_en.q) : reg2hw.es_conf.rct_en.q;
      assign apt_active[ta] =
          rng_bit_en ? ((rng_bit_sel == ta) & reg2hw.es_conf.apt_en.q) : reg2hw.es_conf.apt_en.q;
    end
  endgenerate

  assign rct_max_cnt = reg2hw.es_rct_health.q;

  assign apt_max_cnt = reg2hw.es_apt_health.apt_max.q;
  assign apt_window = reg2hw.es_apt_health.apt_win.q;

  genvar sh;
  generate
    for (sh = 0; sh < RngBusWidth; sh = sh + 1) begin : gen_shtests
      entropy_src_shtests u_entropy_src_shtests (
          .clk_i            (clk_i),
          .rst_ni           (rst_ni),
          .entropy_bit_i    (sfifo_esdig_rdata[sh]),
          .entropy_bit_vld_i(sfifo_esdig_pop),
          .rct_active_i     (rct_active[sh]),
          .rct_max_cnt_i    (rct_max_cnt),
          .apt_active_i     (apt_active[sh]),
          .apt_max_cnt_i    (apt_max_cnt),
          .apt_window_i     (apt_window),
          .rct_fail_pls_o   (rct_fail_pls[sh]),
          .apt_fail_pls_o   (apt_fail_pls[sh]),
          .shtests_passing_o(shtests_passing[sh])
      );
    end
  endgenerate

  assign event_es_rct_failed = |rct_fail_pls;
  assign event_es_apt_failed = |apt_fail_pls;


  //--------------------------------------------
  // fifos for final distribution
  //--------------------------------------------

  assign fill_sfifo_essw = es_enable & sfifo_essw_not_full & efuse_es_sw_reg_en_i;

  // this fifo feeds the sw register interface

  prim_fifo_sync #(
      .Width(32),
      .Pass(0),
      .Depth(4)
  ) u_prim_fifo_sync_essw (
      .clk_i   (clk_i),
      .rst_ni  (rst_ni),
      .clr_i   (sfifo_essw_clr),
      .wvalid_i(sfifo_essw_push),
      .wready_o(sfifo_essw_not_full),
      .wdata_i (sfifo_essw_wdata),
      .rvalid_o(sfifo_essw_not_empty),
      .rready_i(sfifo_essw_pop),
      .rdata_o (sfifo_essw_rdata),
      .depth_o (sfifo_essw_depth)
  );

  // fifo controls
  assign sfifo_essw_push = es_enable & sfifo_postht_pop & fill_sfifo_essw;
  assign sfifo_essw_clr = ~es_enable;
  assign sfifo_essw_wdata = sfifo_postht_rdata;
  assign sfifo_essw_pop = es_enable & esentropy_rd_pls & efuse_es_sw_reg_en_i;

  // fifo err
  assign sfifo_essw_err =
      (sfifo_essw_push & ~sfifo_essw_not_full) | (sfifo_essw_pop & ~sfifo_essw_not_empty);

  // set the es entropy to the read reg
  assign hw2reg.es_entropy.d = es_enable ? sfifo_essw_rdata : '0;
  assign esentropy_rd_pls = reg2hw.es_entropy.re;

  // threshold
  assign es_fifo_thresh = reg2hw.es_thresh.q;

  // entropy valid
  assign entropy_val_d = ~es_enable ? 1'b0 : (sfifo_essw_depth >= es_fifo_thresh);

  // set the es fifo depth to the read reg
  assign hw2reg.es_fdepthst.d = sfifo_essw_depth;



  // this fifo feeds the hw bus interface

  prim_fifo_sync #(
      .Width(32),
      .Pass(0),
      .Depth(4)
  ) u_prim_fifo_sync_eshw (
      .clk_i   (clk_i),
      .rst_ni  (rst_ni),
      .clr_i   (sfifo_eshw_clr),
      .wvalid_i(sfifo_eshw_push),
      .wready_o(sfifo_eshw_not_full),
      .wdata_i (sfifo_eshw_wdata),
      .rvalid_o(sfifo_eshw_not_empty),
      .rready_i(sfifo_eshw_pop),
      .rdata_o (sfifo_eshw_rdata),
      .depth_o (sfifo_eshw_depth)
  );

  // fifo controls
  assign sfifo_eshw_push = es_enable & sfifo_postht_pop & ~fill_sfifo_essw;
  assign sfifo_eshw_clr = ~es_enable;
  assign sfifo_eshw_wdata = sfifo_postht_rdata;
  assign sfifo_eshw_pop = es_enable & entropy_src_hw_if_i.entropy_src_rdy & sfifo_eshw_not_empty;

  // fifo err
  assign sfifo_eshw_err =
      (sfifo_eshw_push & ~sfifo_eshw_not_full) | (sfifo_eshw_pop & ~sfifo_eshw_not_empty);

  // drive out hw interface
  assign entropy_src_hw_if_o.entropy_src_vld = sfifo_eshw_not_empty;
  assign entropy_src_hw_if_o.entropy_src_bits = sfifo_eshw_rdata;

  //--------------------------------------------
  // diag settings
  //--------------------------------------------

  assign hw2reg.es_fifo_status.diag.d = reg2hw.es_regen.q & (&reg2hw.es_entropy.q);

endmodule
