// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// OTBN mask accelerator interface

module otbn_mai
  import otbn_pkg::*; (
  input  logic clk_i,
  input  logic rst_ni,

  // Secure wipe
  input  logic mai_wipe_i,
  input  logic sec_wipe_running_i,

  // CSR write
  input  logic        ispr_mai_ctrl_wr_i,
  input  logic [31:0] ispr_mai_ctrl_wdata_i,

  // CSR read
  output logic [31:0] ispr_mai_ctrl_rdata_o,
  output logic [31:0] ispr_mai_status_rdata_o,

  // WSR write
  input  logic               ispr_mai_in0_s0_wr_i,
  input  logic               ispr_mai_in0_s0_sec_wipe_i,
  input  logic [ExtWLEN-1:0] ispr_mai_in0_s0_wdata_i,
  input  logic               ispr_mai_in0_s1_wr_i,
  input  logic               ispr_mai_in0_s1_sec_wipe_i,
  input  logic [ExtWLEN-1:0] ispr_mai_in0_s1_wdata_i,
  input  logic               ispr_mai_in1_s0_wr_i,
  input  logic               ispr_mai_in1_s0_sec_wipe_i,
  input  logic [ExtWLEN-1:0] ispr_mai_in1_s0_wdata_i,
  input  logic               ispr_mai_in1_s1_wr_i,
  input  logic               ispr_mai_in1_s1_sec_wipe_i,
  input  logic [ExtWLEN-1:0] ispr_mai_in1_s1_wdata_i,
  input  logic               ispr_mai_res_s0_wr_i,
  input  logic               ispr_mai_res_s0_sec_wipe_i,
  input  logic [ExtWLEN-1:0] ispr_mai_res_s0_wdata_i,
  input  logic               ispr_mai_res_s1_wr_i,
  input  logic               ispr_mai_res_s1_sec_wipe_i,
  input  logic [ExtWLEN-1:0] ispr_mai_res_s1_wdata_i,

  // WSR read
  output logic [ExtWLEN-1:0] ispr_mai_in0_s0_rdata_o,
  output logic [ExtWLEN-1:0] ispr_mai_in0_s1_rdata_o,
  output logic [ExtWLEN-1:0] ispr_mai_in1_s0_rdata_o,
  output logic [ExtWLEN-1:0] ispr_mai_in1_s1_rdata_o,
  output logic [ExtWLEN-1:0] ispr_mai_res_s0_rdata_o,
  output logic [ExtWLEN-1:0] ispr_mai_res_s1_rdata_o,

  // Connection to MOD register with integrity data
  input  logic [ExtWLEN-1:0] ispr_mod_intg_i,

  // Error
  output logic mai_software_error_o,
  output logic mai_reg_intg_violation_err_o,
  output logic mai_state_err_o,

  input  logic [UrndLen-1:0] urnd_data_i
);

  ///////////
  // Types //
  ///////////

  localparam int unsigned IsprMaiCtrlResWidth  = 32'd32 - 32'd1 - MaskOpWidth;

  typedef struct packed {
    logic [IsprMaiCtrlResWidth-1:0] rsvd;
    mask_op_e                       op;
    logic                           start;
  } ispr_mai_ctrl_t;

  typedef union packed {
    ispr_mai_ctrl_t csr;
    logic [31:0]    bus;
  } ispr_mai_ctrl_u_t;

  typedef struct packed {
    logic [31-2:0] rsvd;
    logic          ready;
    logic          busy;
  } ispr_mai_status_t;

  typedef union packed {
    ispr_mai_status_t csr;
    logic [31:0]      bus;
  } ispr_mai_status_u_t;

  localparam int unsigned MaiEccWidth = BaseIntgWidth - 32'd32;

  typedef struct packed {
    logic [MaiEccWidth-1:0] intg;
    logic [31:0]            word;
  } otbn_base_intg_word_t;

  typedef union packed {
    logic [ExtWLEN-1:0]                          bus;
    otbn_base_intg_word_t [BaseWordsPerWLEN-1:0] intgword;
  } ispr_mai_u_t;

  typedef struct packed {
    logic out_cnt;
    logic in_cnt;
    logic ma_fifo;
    logic ma_cnt;
  } mai_state_err_t;

  typedef struct packed {
    logic [1:0] mod;
    logic [1:0] in0_s0;
    logic [1:0] in0_s1;
    logic [1:0] in1_s0;
    logic [1:0] in1_s1;
  } mai_reg_intg_violation_err_t;

  typedef struct packed {
    logic invalid_op;
    logic busy_start;
    logic busy_write;
    logic rsvd_csr_write;
  } ispr_mai_sw_err_t;

  localparam int unsigned MaiIsprRndRsvdWidth  = UrndLen - ExtWLEN;

  typedef struct packed {
    logic [MaiIsprRndRsvdWidth-1:0] rsvd;
    logic [ExtWLEN-1:0]             urnd;
  } mai_ispr_urnd_t;

  localparam int unsigned MaiMaRndRsvdWidth  = UrndLen - 32'd322 - 32'd32 - 32'd32 - 32'd3;

  typedef struct packed {
    logic [MaiMaRndRsvdWidth-1:0] rsvd;
    logic [  2:0]                 cnt;
    logic [ 31:0]                 mask_1;
    logic [ 31:0]                 mask_0;
    logic [321:0]                 urnd;
  } mai_ma_urnd_t;

  localparam int unsigned MaiMaWipeRndRsvdWidth  = UrndLen - 32'd5 * 32'd32;

  typedef struct packed {
    logic [MaiMaWipeRndRsvdWidth-1:0] rsvd;
    logic [31:0]                      mod;
    logic [31:0]                      in1_s1;
    logic [31:0]                      in1_s0;
    logic [31:0]                      in0_s1;
    logic [31:0]                      in0_s0;
  } mai_ma_wipe_urnd_t;

  typedef union packed {
    logic [UrndLen-1:0] bus;
    mai_ispr_urnd_t     ispr;
    mai_ma_urnd_t       ma;
    mai_ma_wipe_urnd_t  wipe;
  } mai_urnd_u_t;

  localparam int unsigned MaiCntWidth = prim_util_pkg::vbits(BaseWordsPerWLEN);

  typedef logic [MaiCntWidth-1:0] mai_cnt_t;


  /////////////
  // Signals //
  /////////////

  // PRNG input
  mai_urnd_u_t mai_urnd;
  logic        unused_urnd;

  // Error signals
  mai_reg_intg_violation_err_t mai_reg_intg_violation_err;
  logic                        mai_reg_intg_violation_err_masked;
  mai_state_err_t              mai_state_err;

  // Masking accelerator signals
  logic        ma_in_valid_q;
  logic        ma_in_ready;
  logic        ma_in_consume;
  logic        ma_out_ready;
  logic        ma_busy_q;
  logic [31:0] ma_in0[32'd2];
  logic [31:0] ma_in1[32'd2];
  logic [31:0] ma_remask_rand[32'd2];
  logic [31:0] ma_result[32'd2];
  ispr_mai_u_t ma_mod;
  logic [31:0] ma_mod_lsw;

  // Input counter
  mai_cnt_t in_cnt_load_val_q;
  mai_cnt_t in_cnt_tgt;
  logic     in_cnt_overflow;
  logic     in_cnt_done;
  logic     in_cnt_set;

  // Input multiplexer
  otbn_base_intg_word_t ispr_mai_in0_s0_mux_in[BaseWordsPerWLEN];
  otbn_base_intg_word_t ispr_mai_in0_s1_mux_in[BaseWordsPerWLEN];
  otbn_base_intg_word_t ispr_mai_in1_s0_mux_in[BaseWordsPerWLEN];
  otbn_base_intg_word_t ispr_mai_in1_s1_mux_in[BaseWordsPerWLEN];

  mai_cnt_t                    ispr_mai_in_mux_sel;
  logic [BaseWordsPerWLEN-1:0] ispr_mai_in_mux_sel_onehot;

  otbn_base_intg_word_t ispr_mai_in0_s0_mux_out;
  otbn_base_intg_word_t ispr_mai_in0_s1_mux_out;
  otbn_base_intg_word_t ispr_mai_in1_s0_mux_out;
  otbn_base_intg_word_t ispr_mai_in1_s1_mux_out;

  // Output counter
  mai_cnt_t out_cnt_load_val_d, out_cnt_load_val_q;
  mai_cnt_t out_cnt_tgt;
  logic     out_cnt_overflow;
  logic     out_cnt_done;
  logic     out_cnt_set;

  // Output multiplexer
  mai_cnt_t                    ispr_mai_out_demux_sel;
  logic [BaseWordsPerWLEN-1:0] ispr_mai_out_demux_sel_onehot;

  otbn_base_intg_word_t ispr_mai_res_s0;
  otbn_base_intg_word_t ispr_mai_res_s1;

  // CSRs
  ispr_mai_ctrl_u_t   ispr_mai_ctrl_r;
  ispr_mai_ctrl_u_t   ispr_mai_ctrl_w;
  ispr_mai_status_u_t ispr_mai_status;
  logic               ma_start;
  mask_op_e           ma_mask_op_q;
  ispr_mai_sw_err_t   ispr_mai_sw_err;

  // WSRs
  ispr_mai_u_t ispr_mai_in0_s0_d, ispr_mai_in0_s0_q;
  ispr_mai_u_t ispr_mai_in0_s1_d, ispr_mai_in0_s1_q;
  ispr_mai_u_t ispr_mai_in1_s0_d, ispr_mai_in1_s0_q;
  ispr_mai_u_t ispr_mai_in1_s1_d, ispr_mai_in1_s1_q;
  ispr_mai_u_t ispr_mai_res_s0_d, ispr_mai_res_s0_q;
  ispr_mai_u_t ispr_mai_res_s1_d, ispr_mai_res_s1_q;


  ////////////
  // Random //
  ////////////
  assign mai_urnd.bus = urnd_data_i;
  assign unused_urnd  = ^{mai_urnd.ma.rsvd, mai_urnd.ispr.rsvd, mai_urnd.wipe.rsvd};


  /////////////////////////
  // Masking Accelerator //
  /////////////////////////

  otbn_mask_accelerator u_otbn_mask_accelerator (
    .clk_i,
    .rst_ni,
    .sec_wipe_running_i,
    .wvalid_i       (ma_in_valid_q),
    .wready_o       (ma_in_ready),
    .in0_i          (ma_in0),
    .in1_i          (ma_in1),
    .rand_i         (mai_urnd.ma.urnd),
    .remask_rand_i  (ma_remask_rand),
    .mod_i          (ma_mod_lsw),
    .mask_op_i      (ma_mask_op_q),
    .rvalid_o       (ma_out_ready),
    .rready_i       (1'b0),             // Internally ignored
    .result_o       (ma_result),
    .mask_fifo_err_o(mai_state_err.ma_fifo),
    .ctr_err_o      (mai_state_err.ma_cnt)
  );

  // We only feed valid data if no security wipe is ongoing, otherwise we feed urnd
  assign ma_in0[0] = sec_wipe_running_i ? mai_urnd.wipe.in0_s0 : ispr_mai_in0_s0_mux_out.word;
  assign ma_in0[1] = sec_wipe_running_i ? mai_urnd.wipe.in0_s1 : ispr_mai_in0_s1_mux_out.word;
  assign ma_in1[0] = sec_wipe_running_i ? mai_urnd.wipe.in1_s0 : ispr_mai_in1_s0_mux_out.word;
  assign ma_in1[1] = sec_wipe_running_i ? mai_urnd.wipe.in1_s1 : ispr_mai_in1_s1_mux_out.word;

  assign ma_mod.bus = ispr_mod_intg_i;
  assign ma_mod_lsw = sec_wipe_running_i ? mai_urnd.wipe.mod : ma_mod.intgword[0].word;

  // We only use the lowest word
  logic unused_ma_mod;
  assign unused_ma_mod = ^ma_mod;

  assign ma_remask_rand[0] = mai_urnd.ma.mask_0;
  assign ma_remask_rand[1] = mai_urnd.ma.mask_1;

  assign ma_in_consume = ma_in_valid_q & ma_in_ready;

  // Integrity check of the lowest word of ispr_mod_intg_i
  prim_secded_inv_39_32_dec u_prim_secded_inv_39_32_dec_mod (
    .data_i    (ma_mod.intgword[0]),
    .data_o    (/* NOT CONNECTED */),
    .syndrome_o(/* NOT CONNECTED */),
    .err_o     (mai_reg_intg_violation_err.mod)
  );

  ////////////////////
  // Input Handling //
  ////////////////////

  prim_count #(
    .Width(MaiCntWidth),
    .PossibleActions(prim_count_pkg::Clr | prim_count_pkg::Set | prim_count_pkg::Incr)
  ) u_prim_count_input_word_select (
    .clk_i,
    .rst_ni,
    .clr_i             (in_cnt_overflow && !in_cnt_done && !mai_wipe_i),
    .set_i             (in_cnt_set),
    .set_cnt_i         (mai_urnd.ma.cnt),
    .incr_en_i         (1'b1),
    .decr_en_i         (1'b0),
    .step_i            (mai_cnt_t'('d1)),
    .commit_i          (ma_in_consume || in_cnt_set),
    .cnt_o             (ispr_mai_in_mux_sel),
    .cnt_after_commit_o(/* NOT CONNECTED */),
    .err_o             (mai_state_err.in_cnt)
  );

  assign in_cnt_tgt      = (in_cnt_load_val_q - mai_cnt_t'('d1));
  assign in_cnt_done     = ispr_mai_in_mux_sel == in_cnt_tgt;
  assign in_cnt_overflow = ispr_mai_in_mux_sel == '1;
  assign in_cnt_set      = in_cnt_done || mai_wipe_i;

  // Store initial value of input counter
  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_init_in_cnt_load_val_store
    if (!rst_ni) begin
      in_cnt_load_val_q <= '0;
    end else begin
      if (in_cnt_set) begin
        in_cnt_load_val_q <= mai_urnd.ma.cnt;
      end
    end
  end

  // Input word selection signal to one hot
  prim_onehot_enc #(
    .OneHotWidth(BaseWordsPerWLEN)
  ) u_prim_onehot_enc_input_word_select (
    .in_i (ispr_mai_in_mux_sel),
    .en_i (ma_in_valid_q),
    .out_o(ispr_mai_in_mux_sel_onehot)
  );

  // Unpack inputs
  for (genvar i = 0; i < BaseWordsPerWLEN; i++) begin : gen_in_mux_connect
    assign ispr_mai_in0_s0_mux_in[i] = ispr_mai_in0_s0_q.intgword[i];
    assign ispr_mai_in0_s1_mux_in[i] = ispr_mai_in0_s1_q.intgword[i];
    assign ispr_mai_in1_s0_mux_in[i] = ispr_mai_in1_s0_q.intgword[i];
    assign ispr_mai_in1_s1_mux_in[i] = ispr_mai_in1_s1_q.intgword[i];
  end

  prim_onehot_mux #(
    .Width(BaseIntgWidth),
    .Inputs(BaseWordsPerWLEN)
  ) u_prim_onehot_mux_in0_s0 (
    .clk_i,
    .rst_ni,
    .in_i (ispr_mai_in0_s0_mux_in),
    .sel_i(ispr_mai_in_mux_sel_onehot),
    .out_o(ispr_mai_in0_s0_mux_out)
  );

  prim_onehot_mux #(
    .Width(BaseIntgWidth),
    .Inputs(BaseWordsPerWLEN)
  ) u_prim_onehot_mux_in0_s1 (
    .clk_i,
    .rst_ni,
    .in_i (ispr_mai_in0_s1_mux_in),
    .sel_i(ispr_mai_in_mux_sel_onehot),
    .out_o(ispr_mai_in0_s1_mux_out)
  );

  prim_onehot_mux #(
    .Width(BaseIntgWidth),
    .Inputs(BaseWordsPerWLEN)
  ) u_prim_onehot_mux_in1_s0 (
    .clk_i,
    .rst_ni,
    .in_i (ispr_mai_in1_s0_mux_in),
    .sel_i(ispr_mai_in_mux_sel_onehot),
    .out_o(ispr_mai_in1_s0_mux_out)
  );

  prim_onehot_mux #(
    .Width(BaseIntgWidth),
    .Inputs(BaseWordsPerWLEN)
  ) u_prim_onehot_mux_in1_s1 (
    .clk_i,
    .rst_ni,
    .in_i (ispr_mai_in1_s1_mux_in),
    .sel_i(ispr_mai_in_mux_sel_onehot),
    .out_o(ispr_mai_in1_s1_mux_out)
  );

  prim_secded_inv_39_32_dec u_prim_secded_inv_39_32_dec_in0_s0 (
    .data_i    (ispr_mai_in0_s0_mux_out),
    .data_o    (/* NOT CONNECTED */),
    .syndrome_o(/* NOT CONNECTED */),
    .err_o     (mai_reg_intg_violation_err.in0_s0)
  );

  prim_secded_inv_39_32_dec u_prim_secded_inv_39_32_dec_in0_s1 (
    .data_i    (ispr_mai_in0_s1_mux_out),
    .data_o    (/* NOT CONNECTED */),
    .syndrome_o(/* NOT CONNECTED */),
    .err_o     (mai_reg_intg_violation_err.in0_s1)
  );

  prim_secded_inv_39_32_dec u_prim_secded_inv_39_32_dec_in1_s0 (
    .data_i    (ispr_mai_in1_s0_mux_out),
    .data_o    (/* NOT CONNECTED */),
    .syndrome_o(/* NOT CONNECTED */),
    .err_o     (mai_reg_intg_violation_err.in1_s0)
  );

  prim_secded_inv_39_32_dec u_prim_secded_inv_39_32_dec_in1_s1 (
    .data_i    (ispr_mai_in1_s1_mux_out),
    .data_o    (/* NOT CONNECTED */),
    .syndrome_o(/* NOT CONNECTED */),
    .err_o     (mai_reg_intg_violation_err.in1_s1)
  );


  /////////////////////
  // Output Handling //
  /////////////////////

  prim_count #(
    .Width(MaiCntWidth),
    .PossibleActions(prim_count_pkg::Clr | prim_count_pkg::Set | prim_count_pkg::Incr)
  ) u_prim_count_output_word_select (
    .clk_i,
    .rst_ni,
    .clr_i             (out_cnt_overflow & !out_cnt_done & !mai_wipe_i),
    .set_i             (out_cnt_set),
    .set_cnt_i         (out_cnt_load_val_d),
    .incr_en_i         (1'b1),
    .decr_en_i         (1'b0),
    .step_i            (mai_cnt_t'('d1)),
    .commit_i          (ma_out_ready || out_cnt_set),
    .cnt_o             (ispr_mai_out_demux_sel),
    .cnt_after_commit_o(/* NOT CONNECTED */),
    .err_o             (mai_state_err.out_cnt)
  );

  assign out_cnt_load_val_d = mai_wipe_i ? mai_urnd.ma.cnt : in_cnt_load_val_q;
  assign out_cnt_tgt        = (out_cnt_load_val_q - mai_cnt_t'('d1));
  assign out_cnt_done       = ispr_mai_out_demux_sel == out_cnt_tgt;
  assign out_cnt_overflow   = ispr_mai_out_demux_sel == '1;
  assign out_cnt_set        = out_cnt_done || mai_wipe_i;

  // Store initial value of output counter
  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_init_out_cnt_load_val_store
    if (!rst_ni) begin
      out_cnt_load_val_q <= '0;
    end else begin
      if (out_cnt_set) begin
        out_cnt_load_val_q <= out_cnt_load_val_d;
      end
    end
  end

  // Output word selection signal to one hot
  // We don't write to the register if a secure wipe is ongoing
  prim_onehot_enc #(
    .OneHotWidth(BaseWordsPerWLEN)
  ) u_prim_onehot_enc_output_word_select (
    .in_i (ispr_mai_out_demux_sel),
    .en_i (ma_out_ready & !sec_wipe_running_i),
    .out_o(ispr_mai_out_demux_sel_onehot)
  );

  prim_secded_inv_39_32_enc u_prim_secded_inv_39_32_enc_res_s0 (
    .data_i(ma_result[0]),
    .data_o(ispr_mai_res_s0)
  );

  prim_secded_inv_39_32_enc u_prim_secded_inv_39_32_enc_res_s1 (
    .data_i(ma_result[1]),
    .data_o(ispr_mai_res_s1)
  );


  ////////////////////
  // CSR Bus Access //
  ////////////////////

  // Control write
  assign ispr_mai_ctrl_w.bus = ispr_mai_ctrl_wdata_i;
  assign ma_start            = ispr_mai_ctrl_wr_i & ispr_mai_ctrl_w.csr.start;

  // Status read
  assign ispr_mai_status.csr.rsvd  = '0;
  assign ispr_mai_status.csr.ready = !ma_in_valid_q;
  assign ispr_mai_status.csr.busy  = ma_busy_q;
  assign ispr_mai_status_rdata_o   = ispr_mai_status.bus;

  // Control read
  assign ispr_mai_ctrl_r.csr.rsvd  = '0;
  assign ispr_mai_ctrl_r.csr.start = 1'b0;
  assign ispr_mai_ctrl_r.csr.op    = ma_mask_op_q;
  assign ispr_mai_ctrl_rdata_o     = ispr_mai_ctrl_r.bus;

  // Erroneous control accesses
  assign ispr_mai_sw_err.busy_start     = ma_start & ma_busy_q;
  assign ispr_mai_sw_err.busy_write     = ma_in_valid_q &
                                          |{ ispr_mai_in0_s0_wr_i, ispr_mai_in0_s1_wr_i,
                                             ispr_mai_in1_s0_wr_i, ispr_mai_in1_s1_wr_i };
  assign ispr_mai_sw_err.rsvd_csr_write = ispr_mai_ctrl_wr_i & (|ispr_mai_ctrl_w.csr.rsvd);
  assign ispr_mai_sw_err.invalid_op     = !(ma_mask_op_q inside
                                          {SecAdd, SecAddMod, ArithToBool, BoolToArith}) & ma_start;

  // Valid control
  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_valid_control_state
    if (!rst_ni) begin
      ma_in_valid_q <= 1'b0;
    end else begin
      if (in_cnt_set) begin
        ma_in_valid_q <= 1'b0;
      end else if (ma_start) begin
        ma_in_valid_q <= 1'b1;
      end
    end
  end

  // Busy control
  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_busy_control_state
    if (!rst_ni) begin
      ma_busy_q <= 1'b0;
    end else begin
      if (out_cnt_set) begin
        ma_busy_q <= 1'b0;
      end else if (ma_start) begin
        ma_busy_q <= 1'b1;
      end
    end
  end

  // Store the operation of the mask accelerator
  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_ma_op_store
    if (!rst_ni) begin
      ma_mask_op_q <= SecAdd;
    end else begin
      if (mai_wipe_i) begin
        ma_mask_op_q <= SecAdd;
      end else if (ispr_mai_ctrl_wr_i) begin
        ma_mask_op_q <= ispr_mai_ctrl_w.csr.op;
      end
    end
  end


  ////////////////////
  // WSR Bus Access //
  ////////////////////

  // WSR bus write access. Wiping takes priority over writing
  assign ispr_mai_in0_s0_d.bus = ispr_mai_in0_s0_sec_wipe_i ? mai_urnd.ispr.urnd      :
                                 ispr_mai_in0_s0_wr_i       ? ispr_mai_in0_s0_wdata_i :
                                 ispr_mai_in0_s0_q.bus;

  assign ispr_mai_in0_s1_d.bus = ispr_mai_in0_s1_sec_wipe_i ? mai_urnd.ispr.urnd      :
                                 ispr_mai_in0_s1_wr_i       ? ispr_mai_in0_s1_wdata_i :
                                 ispr_mai_in0_s1_q.bus;

  assign ispr_mai_in1_s0_d.bus = ispr_mai_in1_s0_sec_wipe_i ? mai_urnd.ispr.urnd      :
                                 ispr_mai_in1_s0_wr_i       ? ispr_mai_in1_s0_wdata_i :
                                 ispr_mai_in1_s0_q.bus;

  assign ispr_mai_in1_s1_d.bus = ispr_mai_in1_s1_sec_wipe_i ? mai_urnd.ispr.urnd      :
                                 ispr_mai_in1_s1_wr_i       ? ispr_mai_in1_s1_wdata_i :
                                 ispr_mai_in1_s1_q.bus;

  always_comb begin : proc_res_s0_next
    // Bus access
    ispr_mai_res_s0_d.bus = ispr_mai_res_s0_sec_wipe_i ? mai_urnd.ispr.urnd      :
                            ispr_mai_res_s0_wr_i       ? ispr_mai_res_s0_wdata_i :
                            ispr_mai_res_s0_q.bus;

    // Accelerator access has prio
    for (int i = 0; i < BaseWordsPerWLEN; i++) begin : gen_word_acc_write_res_s0
      if (ispr_mai_out_demux_sel_onehot[i]) ispr_mai_res_s0_d.intgword[i] = ispr_mai_res_s0;
    end
  end

  always_comb begin : proc_res_s1_next
    // Bus access
    ispr_mai_res_s1_d.bus = ispr_mai_res_s1_sec_wipe_i ? mai_urnd.ispr.urnd      :
                            ispr_mai_res_s1_wr_i       ? ispr_mai_res_s1_wdata_i :
                            ispr_mai_res_s1_q.bus;

    // Accelerator access has priority
    for (int i = 0; i < BaseWordsPerWLEN; i++) begin : gen_word_acc_write_res_s1
      if (ispr_mai_out_demux_sel_onehot[i]) ispr_mai_res_s1_d.intgword[i] = ispr_mai_res_s1;
    end
  end

  // WSR bus read access
  // always present the output of the registers, the ISPR multiplexing logic blanks the signals
  assign ispr_mai_in0_s0_rdata_o = ispr_mai_in0_s0_q.bus;
  assign ispr_mai_in0_s1_rdata_o = ispr_mai_in0_s1_q.bus;
  assign ispr_mai_in1_s0_rdata_o = ispr_mai_in1_s0_q.bus;
  assign ispr_mai_in1_s1_rdata_o = ispr_mai_in1_s1_q.bus;
  assign ispr_mai_res_s0_rdata_o = ispr_mai_res_s0_q.bus;
  assign ispr_mai_res_s1_rdata_o = ispr_mai_res_s1_q.bus;

  // WSR data store
  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_wsr_data_store
    if (!rst_ni) begin
      ispr_mai_in0_s0_q <= '0;
      ispr_mai_in0_s1_q <= '0;
      ispr_mai_in1_s0_q <= '0;
      ispr_mai_in1_s1_q <= '0;
      ispr_mai_res_s0_q <= '0;
      ispr_mai_res_s1_q <= '0;
    end else begin
      ispr_mai_in0_s0_q <= ispr_mai_in0_s0_d;
      ispr_mai_in0_s1_q <= ispr_mai_in0_s1_d;
      ispr_mai_in1_s0_q <= ispr_mai_in1_s0_d;
      ispr_mai_in1_s1_q <= ispr_mai_in1_s1_d;
      ispr_mai_res_s0_q <= ispr_mai_res_s0_d;
      ispr_mai_res_s1_q <= ispr_mai_res_s1_d;
    end
  end


  ////////////////////
  // Error Handling //
  ////////////////////

  // Calculate the masked ECC integrity error signal
  always_comb begin : proc_mai_reg_intg_violation_err_masked
    mai_reg_intg_violation_err_masked = 1'b1;
    unique case (ma_mask_op_q)
      // All input words but not the mod least significant word of the mod register
      SecAdd: begin
        mai_reg_intg_violation_err_masked = (|mai_reg_intg_violation_err.in0_s0) |
                                            (|mai_reg_intg_violation_err.in0_s1) |
                                            (|mai_reg_intg_violation_err.in1_s0) |
                                            (|mai_reg_intg_violation_err.in1_s1);
      end
      // All inputs
      SecAddMod: begin
        mai_reg_intg_violation_err_masked = (|mai_reg_intg_violation_err.in0_s0) |
                                            (|mai_reg_intg_violation_err.in0_s1) |
                                            (|mai_reg_intg_violation_err.in1_s0) |
                                            (|mai_reg_intg_violation_err.in1_s1) |
                                            (|mai_reg_intg_violation_err.mod);
      end
      // Input 0 and the least significant word of the mod register
      ArithToBool, BoolToArith: begin
        mai_reg_intg_violation_err_masked = (|mai_reg_intg_violation_err.in0_s0) |
                                            (|mai_reg_intg_violation_err.in0_s1) |
                                            (|mai_reg_intg_violation_err.mod);
      end
      default:;
    endcase
  end

  // An integrity error happens if we access an invalid word
  assign mai_reg_intg_violation_err_o = mai_reg_intg_violation_err_masked & ma_in_consume;
  // State errors
  assign mai_state_err_o              = |mai_state_err;
  // Sw error
  assign mai_software_error_o         = |ispr_mai_sw_err;

endmodule
