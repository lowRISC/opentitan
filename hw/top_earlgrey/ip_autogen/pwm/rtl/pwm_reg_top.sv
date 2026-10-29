// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Register Top module, with the per-channel registers generated over NOutputs

`include "prim_assert.sv"

module pwm_reg_top
  # (
    parameter int unsigned NOutputs             = 6,
    parameter bit          EnableRacl           = 1'b0,
    parameter bit          RaclErrorRsp         = 1'b1,
    parameter top_racl_pkg::racl_policy_sel_t
      RaclPolicySelVec[pwm_reg_pkg::pwm_num_regs(NOutputs)] =
        '{pwm_reg_pkg::pwm_num_regs(NOutputs){0}}
  ) (
  input clk_i,
  input rst_ni,
  input clk_core_i,
  input rst_core_ni,
  input  tlul_pkg::tl_h2d_t tl_i,
  output tlul_pkg::tl_d2h_t tl_o,
  // To HW
  output pwm_reg_pkg::pwm_reg2hw_alert_test_reg_t                  reg2hw_alert_test_o,
  output pwm_reg_pkg::pwm_reg2hw_cfg_reg_t                         reg2hw_cfg_o,
  output pwm_reg_pkg::pwm_reg2hw_pwm_en_mreg_t      [NOutputs-1:0] reg2hw_pwm_en_o,
  output pwm_reg_pkg::pwm_reg2hw_invert_mreg_t      [NOutputs-1:0] reg2hw_invert_o,
  output pwm_reg_pkg::pwm_reg2hw_pwm_param_mreg_t   [NOutputs-1:0] reg2hw_pwm_param_o,
  output pwm_reg_pkg::pwm_reg2hw_duty_cycle_mreg_t  [NOutputs-1:0] reg2hw_duty_cycle_o,
  output pwm_reg_pkg::pwm_reg2hw_blink_param_mreg_t [NOutputs-1:0] reg2hw_blink_param_o,

  // RACL interface
  input  top_racl_pkg::racl_policy_vec_t racl_policies_i,
  output top_racl_pkg::racl_error_log_t  racl_error_o,

  // Integrity check errors
  output logic intg_err_o
);

  import pwm_reg_pkg::* ;

  localparam int NumRegs = pwm_num_regs(NOutputs);
  localparam int AW = pwm_block_aw(NOutputs);
  localparam int DW = 32;
  localparam int DBW = DW/8;                    // Byte Width

  if (!(NOutputs >= 1 && NOutputs <= 32)) begin : gen_bad_noutputs
    $error("NOutputs must be in the range [1, 32]");
  end

  // Register offsets and indices. The per-channel registers follow INVERT, NOutputs of each.
  localparam logic [AW-1:0] PWM_ALERT_TEST_OFFSET = AW'('h0);
  localparam logic [AW-1:0] PWM_REGWEN_OFFSET     = AW'('h4);
  localparam logic [AW-1:0] PWM_CFG_OFFSET        = AW'('h8);
  localparam logic [AW-1:0] PWM_PWM_EN_OFFSET     = AW'('hc);
  localparam logic [AW-1:0] PWM_INVERT_OFFSET     = AW'('h10);
  localparam int PwmParamIdx   = 5;
  localparam int DutyCycleIdx  = PwmParamIdx + NOutputs;
  localparam int BlinkParamIdx = DutyCycleIdx + NOutputs;

  // PWM_EN and INVERT hold one bit per channel; writes must enable every byte that holds one.
  localparam logic [3:0] ChanBitsPermit = 4'((1 << ((NOutputs + 7) / 8)) - 1);

  // register signals
  logic           reg_we;
  logic           reg_re;
  logic [AW-1:0]  reg_addr;
  logic [DW-1:0]  reg_wdata;
  logic [DBW-1:0] reg_be;
  logic [DW-1:0]  reg_rdata;
  logic           reg_error;

  logic          addrmiss, wr_err;

  logic [DW-1:0] reg_rdata_next;
  logic reg_busy;

  tlul_pkg::tl_h2d_t tl_reg_h2d;
  tlul_pkg::tl_d2h_t tl_reg_d2h;


  // incoming payload check
  logic intg_err;
  tlul_cmd_intg_chk u_chk (
    .tl_i(tl_i),
    .err_o(intg_err)
  );

  // also check for spurious write enables
  logic reg_we_err;
  logic [NumRegs-1:0] reg_we_check;
  prim_reg_we_check #(
    .OneHotWidth(NumRegs)
  ) u_prim_reg_we_check (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .oh_i  (reg_we_check),
    .en_i  (reg_we && !addrmiss),
    .err_o (reg_we_err)
  );

  logic err_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      err_q <= '0;
    end else if (intg_err || reg_we_err) begin
      err_q <= 1'b1;
    end
  end

  // integrity error output is permanent and should be used for alert generation
  // register errors are transactional
  assign intg_err_o = err_q | intg_err | reg_we_err;

  // outgoing integrity generation
  tlul_pkg::tl_d2h_t tl_o_pre;
  tlul_rsp_intg_gen #(
    .EnableRspIntgGen(1),
    .EnableDataIntgGen(1)
  ) u_rsp_intg_gen (
    .tl_i(tl_o_pre),
    .tl_o(tl_o)
  );

  assign tl_reg_h2d = tl_i;
  assign tl_o_pre   = tl_reg_d2h;

  tlul_adapter_reg #(
    .RegAw(AW),
    .RegDw(DW),
    .EnableDataIntgGen(0)
  ) u_reg_if (
    .clk_i  (clk_i),
    .rst_ni (rst_ni),

    .tl_i (tl_reg_h2d),
    .tl_o (tl_reg_d2h),

    .en_ifetch_i(prim_mubi_pkg::MuBi4False),
    .intg_error_o(),

    .we_o    (reg_we),
    .re_o    (reg_re),
    .addr_o  (reg_addr),
    .wdata_o (reg_wdata),
    .be_o    (reg_be),
    .busy_i  (reg_busy),
    .rdata_i (reg_rdata),
    // Translate RACL error to TLUL error if enabled
    .error_i (reg_error | (RaclErrorRsp & racl_error_o.valid))
  );

  // cdc oversampling signals

  assign reg_rdata = reg_rdata_next ;
  assign reg_error = addrmiss | wr_err | intg_err;

  // Define SW related signals
  // Format: <reg>_<field>_{wd|we|qs}
  //        or <reg>_{wd|we|qs} if field == 1 or 0
  logic alert_test_we;
  logic alert_test_wd;
  logic regwen_we;
  logic regwen_qs;
  logic regwen_wd;
  logic cfg_we;
  logic [31:0] cfg_qs;
  logic cfg_busy;
  logic pwm_en_we;
  logic [NOutputs-1:0] pwm_en_qs;
  logic pwm_en_busy;
  logic invert_we;
  logic [NOutputs-1:0] invert_qs;
  logic invert_busy;
  logic [NOutputs-1:0] pwm_param_we;
  logic [NOutputs-1:0][31:0] pwm_param_qs;
  logic [NOutputs-1:0] pwm_param_busy;
  logic [NOutputs-1:0] duty_cycle_we;
  logic [NOutputs-1:0][31:0] duty_cycle_qs;
  logic [NOutputs-1:0] duty_cycle_busy;
  logic [NOutputs-1:0] blink_param_we;
  logic [NOutputs-1:0][31:0] blink_param_qs;
  logic [NOutputs-1:0] blink_param_busy;
  // Define register CDC handling.
  // CDC handling is done on a per-reg instead of per-field boundary.

  logic [26:0]  core_cfg_clk_div_qs_int;
  logic [3:0]  core_cfg_dc_resn_qs_int;
  logic  core_cfg_cntr_en_qs_int;
  logic [31:0] core_cfg_qs;
  logic [31:0] core_cfg_wdata;
  logic core_cfg_we;
  logic unused_core_cfg_wdata;
  logic core_cfg_regwen;

  always_comb begin
    core_cfg_qs = 32'h38008000;
    core_cfg_qs[26:0] = core_cfg_clk_div_qs_int;
    core_cfg_qs[30:27] = core_cfg_dc_resn_qs_int;
    core_cfg_qs[31] = core_cfg_cntr_en_qs_int;
  end

  prim_reg_cdc #(
    .DataWidth(32),
    .ResetVal(32'h38008000),
    .BitMask(32'hffffffff),
    .DstWrReq(0)
  ) u_cfg_cdc (
    .clk_src_i    (clk_i),
    .rst_src_ni   (rst_ni),
    .clk_dst_i    (clk_core_i),
    .rst_dst_ni   (rst_core_ni),
    .src_regwen_i (regwen_qs),
    .src_we_i     (cfg_we),
    .src_re_i     ('0),
    .src_wd_i     (reg_wdata[31:0]),
    .src_busy_o   (cfg_busy),
    .src_qs_o     (cfg_qs), // for software read back
    .dst_update_i ('0),
    .dst_ds_i     ('0),
    .dst_qs_i     (core_cfg_qs),
    .dst_we_o     (core_cfg_we),
    .dst_re_o     (),
    .dst_regwen_o (core_cfg_regwen),
    .dst_wd_o     (core_cfg_wdata)
  );
  assign unused_core_cfg_wdata =
      ^core_cfg_wdata;

  logic [NOutputs-1:0] core_pwm_en_qs;
  logic [NOutputs-1:0] core_pwm_en_wdata;
  logic core_pwm_en_we;
  logic unused_core_pwm_en_wdata;
  logic core_pwm_en_regwen;

  prim_reg_cdc #(
    .DataWidth(NOutputs),
    .ResetVal('0),
    .BitMask('1),
    .DstWrReq(0)
  ) u_pwm_en_cdc (
    .clk_src_i    (clk_i),
    .rst_src_ni   (rst_ni),
    .clk_dst_i    (clk_core_i),
    .rst_dst_ni   (rst_core_ni),
    .src_regwen_i (regwen_qs),
    .src_we_i     (pwm_en_we),
    .src_re_i     ('0),
    .src_wd_i     (reg_wdata[NOutputs-1:0]),
    .src_busy_o   (pwm_en_busy),
    .src_qs_o     (pwm_en_qs), // for software read back
    .dst_update_i ('0),
    .dst_ds_i     ('0),
    .dst_qs_i     (core_pwm_en_qs),
    .dst_we_o     (core_pwm_en_we),
    .dst_re_o     (),
    .dst_regwen_o (core_pwm_en_regwen),
    .dst_wd_o     (core_pwm_en_wdata)
  );
  assign unused_core_pwm_en_wdata =
      ^core_pwm_en_wdata;
  logic [NOutputs-1:0] core_invert_qs;
  logic [NOutputs-1:0] core_invert_wdata;
  logic core_invert_we;
  logic unused_core_invert_wdata;
  logic core_invert_regwen;

  prim_reg_cdc #(
    .DataWidth(NOutputs),
    .ResetVal('0),
    .BitMask('1),
    .DstWrReq(0)
  ) u_invert_cdc (
    .clk_src_i    (clk_i),
    .rst_src_ni   (rst_ni),
    .clk_dst_i    (clk_core_i),
    .rst_dst_ni   (rst_core_ni),
    .src_regwen_i (regwen_qs),
    .src_we_i     (invert_we),
    .src_re_i     ('0),
    .src_wd_i     (reg_wdata[NOutputs-1:0]),
    .src_busy_o   (invert_busy),
    .src_qs_o     (invert_qs), // for software read back
    .dst_update_i ('0),
    .dst_ds_i     ('0),
    .dst_qs_i     (core_invert_qs),
    .dst_we_o     (core_invert_we),
    .dst_re_o     (),
    .dst_regwen_o (core_invert_regwen),
    .dst_wd_o     (core_invert_wdata)
  );
  assign unused_core_invert_wdata =
      ^core_invert_wdata;

  // Register instances
  // R[alert_test]: V(True)
  logic alert_test_qe;
  logic [0:0] alert_test_flds_we;
  assign alert_test_qe = &alert_test_flds_we;
  prim_subreg_ext #(
    .DW    (1)
  ) u_alert_test (
    .re     (1'b0),
    .we     (alert_test_we),
    .wd     (alert_test_wd),
    .d      ('0),
    .qre    (),
    .qe     (alert_test_flds_we[0]),
    .q      (reg2hw_alert_test_o.q),
    .ds     (),
    .qs     ()
  );
  assign reg2hw_alert_test_o.qe = alert_test_qe;


  // R[regwen]: V(False)
  prim_subreg #(
    .DW      (1),
    .SwAccess(prim_subreg_pkg::SwAccessW0C),
    .RESVAL  (1'h1),
    .Mubi    (1'b0)
  ) u_regwen (
    .clk_i   (clk_i),
    .rst_ni  (rst_ni),

    // from register interface
    .we     (regwen_we),
    .wd     (regwen_wd),

    // from internal hardware
    .de     (1'b0),
    .d      ('0),

    // to internal hardware
    .qe     (),
    .q      (),
    .ds     (),

    // to register interface (read)
    .qs     (regwen_qs)
  );


  // R[cfg]: V(False)
  logic cfg_qe;
  logic [2:0] cfg_flds_we;
  prim_flop #(
    .Width(1),
    .ResetValue(0)
  ) u_cfg0_qe (
    .clk_i(clk_core_i),
    .rst_ni(rst_core_ni),
    .d_i(&cfg_flds_we),
    .q_o(cfg_qe)
  );
  // Create REGWEN-gated WE signal
  logic core_cfg_gated_we;
  assign core_cfg_gated_we = core_cfg_we & core_cfg_regwen;
  //   F[clk_div]: 26:0
  prim_subreg #(
    .DW      (27),
    .SwAccess(prim_subreg_pkg::SwAccessRW),
    .RESVAL  (27'h8000),
    .Mubi    (1'b0)
  ) u_cfg_clk_div (
    .clk_i   (clk_core_i),
    .rst_ni  (rst_core_ni),

    // from register interface
    .we     (core_cfg_gated_we),
    .wd     (core_cfg_wdata[26:0]),

    // from internal hardware
    .de     (1'b0),
    .d      ('0),

    // to internal hardware
    .qe     (cfg_flds_we[0]),
    .q      (reg2hw_cfg_o.clk_div.q),
    .ds     (),

    // to register interface (read)
    .qs     (core_cfg_clk_div_qs_int)
  );
  assign reg2hw_cfg_o.clk_div.qe = cfg_qe;

  //   F[dc_resn]: 30:27
  prim_subreg #(
    .DW      (4),
    .SwAccess(prim_subreg_pkg::SwAccessRW),
    .RESVAL  (4'h7),
    .Mubi    (1'b0)
  ) u_cfg_dc_resn (
    .clk_i   (clk_core_i),
    .rst_ni  (rst_core_ni),

    // from register interface
    .we     (core_cfg_gated_we),
    .wd     (core_cfg_wdata[30:27]),

    // from internal hardware
    .de     (1'b0),
    .d      ('0),

    // to internal hardware
    .qe     (cfg_flds_we[1]),
    .q      (reg2hw_cfg_o.dc_resn.q),
    .ds     (),

    // to register interface (read)
    .qs     (core_cfg_dc_resn_qs_int)
  );
  assign reg2hw_cfg_o.dc_resn.qe = cfg_qe;

  //   F[cntr_en]: 31:31
  prim_subreg #(
    .DW      (1),
    .SwAccess(prim_subreg_pkg::SwAccessRW),
    .RESVAL  (1'h0),
    .Mubi    (1'b0)
  ) u_cfg_cntr_en (
    .clk_i   (clk_core_i),
    .rst_ni  (rst_core_ni),

    // from register interface
    .we     (core_cfg_gated_we),
    .wd     (core_cfg_wdata[31]),

    // from internal hardware
    .de     (1'b0),
    .d      ('0),

    // to internal hardware
    .qe     (cfg_flds_we[2]),
    .q      (reg2hw_cfg_o.cntr_en.q),
    .ds     (),

    // to register interface (read)
    .qs     (core_cfg_cntr_en_qs_int)
  );
  assign reg2hw_cfg_o.cntr_en.qe = cfg_qe;


  // R[pwm_en]: V(False)
  logic pwm_en_qe;
  logic [NOutputs-1:0] pwm_en_flds_we;
  prim_flop #(
    .Width(1),
    .ResetValue(0)
  ) u_pwm_en0_qe (
    .clk_i(clk_core_i),
    .rst_ni(rst_core_ni),
    .d_i(&pwm_en_flds_we),
    .q_o(pwm_en_qe)
  );
  // Create REGWEN-gated WE signal
  logic core_pwm_en_gated_we;
  assign core_pwm_en_gated_we = core_pwm_en_we & core_pwm_en_regwen;
  for (genvar i = 0; i < NOutputs; i++) begin : gen_pwm_en
    //   F[en_i]: i:i
    prim_subreg #(
      .DW      (1),
      .SwAccess(prim_subreg_pkg::SwAccessRW),
      .RESVAL  (1'h0),
      .Mubi    (1'b0)
    ) u_pwm_en_en (
      .clk_i   (clk_core_i),
      .rst_ni  (rst_core_ni),

      // from register interface
      .we     (core_pwm_en_gated_we),
      .wd     (core_pwm_en_wdata[i]),

      // from internal hardware
      .de     (1'b0),
      .d      ('0),

      // to internal hardware
      .qe     (pwm_en_flds_we[i]),
      .q      (reg2hw_pwm_en_o[i].q),
      .ds     (),

      // to register interface (read)
      .qs     (core_pwm_en_qs[i])
    );
    assign reg2hw_pwm_en_o[i].qe = pwm_en_qe;
  end


  // R[invert]: V(False)
  logic invert_qe;
  logic [NOutputs-1:0] invert_flds_we;
  prim_flop #(
    .Width(1),
    .ResetValue(0)
  ) u_invert0_qe (
    .clk_i(clk_core_i),
    .rst_ni(rst_core_ni),
    .d_i(&invert_flds_we),
    .q_o(invert_qe)
  );
  // Create REGWEN-gated WE signal
  logic core_invert_gated_we;
  assign core_invert_gated_we = core_invert_we & core_invert_regwen;
  for (genvar i = 0; i < NOutputs; i++) begin : gen_invert
    //   F[invert_i]: i:i
    prim_subreg #(
      .DW      (1),
      .SwAccess(prim_subreg_pkg::SwAccessRW),
      .RESVAL  (1'h0),
      .Mubi    (1'b0)
    ) u_invert_invert (
      .clk_i   (clk_core_i),
      .rst_ni  (rst_core_ni),

      // from register interface
      .we     (core_invert_gated_we),
      .wd     (core_invert_wdata[i]),

      // from internal hardware
      .de     (1'b0),
      .d      ('0),

      // to internal hardware
      .qe     (invert_flds_we[i]),
      .q      (reg2hw_invert_o[i].q),
      .ds     (),

      // to register interface (read)
      .qs     (core_invert_qs[i])
    );
    assign reg2hw_invert_o[i].qe = invert_qe;
  end

  // R[pwm_param_i]: V(False)
  for (genvar i = 0; i < NOutputs; i++) begin : gen_pwm_param
    logic [15:0] core_pwm_param_phase_delay_qs_int;
    logic core_pwm_param_htbt_en_qs_int;
    logic core_pwm_param_blink_en_qs_int;
    logic [31:0] core_pwm_param_qs;
    logic [31:0] core_pwm_param_wdata;
    logic core_pwm_param_we;
    logic unused_core_pwm_param_wdata;
    logic core_pwm_param_regwen;

    always_comb begin
      core_pwm_param_qs = 32'h0;
      core_pwm_param_qs[15:0] = core_pwm_param_phase_delay_qs_int;
      core_pwm_param_qs[30] = core_pwm_param_htbt_en_qs_int;
      core_pwm_param_qs[31] = core_pwm_param_blink_en_qs_int;
    end

    prim_reg_cdc #(
      .DataWidth(32),
      .ResetVal(32'h0),
      .BitMask(32'hc000ffff),
      .DstWrReq(0)
    ) u_pwm_param_cdc (
      .clk_src_i    (clk_i),
      .rst_src_ni   (rst_ni),
      .clk_dst_i    (clk_core_i),
      .rst_dst_ni   (rst_core_ni),
      .src_regwen_i (regwen_qs),
      .src_we_i     (pwm_param_we[i]),
      .src_re_i     ('0),
      .src_wd_i     (reg_wdata[31:0]),
      .src_busy_o   (pwm_param_busy[i]),
      .src_qs_o     (pwm_param_qs[i]), // for software read back
      .dst_update_i ('0),
      .dst_ds_i     ('0),
      .dst_qs_i     (core_pwm_param_qs),
      .dst_we_o     (core_pwm_param_we),
      .dst_re_o     (),
      .dst_regwen_o (core_pwm_param_regwen),
      .dst_wd_o     (core_pwm_param_wdata)
    );
    assign unused_core_pwm_param_wdata =
        ^core_pwm_param_wdata;

    logic pwm_param_qe;
    logic [2:0] pwm_param_flds_we;
    prim_flop #(
      .Width(1),
      .ResetValue(0)
    ) u_pwm_param_qe (
      .clk_i(clk_core_i),
      .rst_ni(rst_core_ni),
      .d_i(&pwm_param_flds_we),
      .q_o(pwm_param_qe)
    );
    // Create REGWEN-gated WE signal
    logic core_pwm_param_gated_we;
    assign core_pwm_param_gated_we = core_pwm_param_we & core_pwm_param_regwen;
    //   F[phase_delay]: 15:0
    prim_subreg #(
      .DW      (16),
      .SwAccess(prim_subreg_pkg::SwAccessRW),
      .RESVAL  (16'h0),
      .Mubi    (1'b0)
    ) u_pwm_param_phase_delay (
      .clk_i   (clk_core_i),
      .rst_ni  (rst_core_ni),

      // from register interface
      .we     (core_pwm_param_gated_we),
      .wd     (core_pwm_param_wdata[15:0]),

      // from internal hardware
      .de     (1'b0),
      .d      ('0),

      // to internal hardware
      .qe     (pwm_param_flds_we[0]),
      .q      (reg2hw_pwm_param_o[i].phase_delay.q),
      .ds     (),

      // to register interface (read)
      .qs     (core_pwm_param_phase_delay_qs_int)
    );
    assign reg2hw_pwm_param_o[i].phase_delay.qe = pwm_param_qe;

    //   F[htbt_en]: 30:30
    prim_subreg #(
      .DW      (1),
      .SwAccess(prim_subreg_pkg::SwAccessRW),
      .RESVAL  (1'h0),
      .Mubi    (1'b0)
    ) u_pwm_param_htbt_en (
      .clk_i   (clk_core_i),
      .rst_ni  (rst_core_ni),

      // from register interface
      .we     (core_pwm_param_gated_we),
      .wd     (core_pwm_param_wdata[30]),

      // from internal hardware
      .de     (1'b0),
      .d      ('0),

      // to internal hardware
      .qe     (pwm_param_flds_we[1]),
      .q      (reg2hw_pwm_param_o[i].htbt_en.q),
      .ds     (),

      // to register interface (read)
      .qs     (core_pwm_param_htbt_en_qs_int)
    );
    assign reg2hw_pwm_param_o[i].htbt_en.qe = pwm_param_qe;

    //   F[blink_en]: 31:31
    prim_subreg #(
      .DW      (1),
      .SwAccess(prim_subreg_pkg::SwAccessRW),
      .RESVAL  (1'h0),
      .Mubi    (1'b0)
    ) u_pwm_param_blink_en (
      .clk_i   (clk_core_i),
      .rst_ni  (rst_core_ni),

      // from register interface
      .we     (core_pwm_param_gated_we),
      .wd     (core_pwm_param_wdata[31]),

      // from internal hardware
      .de     (1'b0),
      .d      ('0),

      // to internal hardware
      .qe     (pwm_param_flds_we[2]),
      .q      (reg2hw_pwm_param_o[i].blink_en.q),
      .ds     (),

      // to register interface (read)
      .qs     (core_pwm_param_blink_en_qs_int)
    );
    assign reg2hw_pwm_param_o[i].blink_en.qe = pwm_param_qe;
  end

  // R[duty_cycle_i]: V(False)
  for (genvar i = 0; i < NOutputs; i++) begin : gen_duty_cycle
    logic [15:0] core_duty_cycle_a_qs_int;
    logic [15:0] core_duty_cycle_b_qs_int;
    logic [31:0] core_duty_cycle_qs;
    logic [31:0] core_duty_cycle_wdata;
    logic core_duty_cycle_we;
    logic unused_core_duty_cycle_wdata;
    logic core_duty_cycle_regwen;

    always_comb begin
      core_duty_cycle_qs = 32'h7fff7fff;
      core_duty_cycle_qs[15:0] = core_duty_cycle_a_qs_int;
      core_duty_cycle_qs[31:16] = core_duty_cycle_b_qs_int;
    end

    prim_reg_cdc #(
      .DataWidth(32),
      .ResetVal(32'h7fff7fff),
      .BitMask(32'hffffffff),
      .DstWrReq(0)
    ) u_duty_cycle_cdc (
      .clk_src_i    (clk_i),
      .rst_src_ni   (rst_ni),
      .clk_dst_i    (clk_core_i),
      .rst_dst_ni   (rst_core_ni),
      .src_regwen_i (regwen_qs),
      .src_we_i     (duty_cycle_we[i]),
      .src_re_i     ('0),
      .src_wd_i     (reg_wdata[31:0]),
      .src_busy_o   (duty_cycle_busy[i]),
      .src_qs_o     (duty_cycle_qs[i]), // for software read back
      .dst_update_i ('0),
      .dst_ds_i     ('0),
      .dst_qs_i     (core_duty_cycle_qs),
      .dst_we_o     (core_duty_cycle_we),
      .dst_re_o     (),
      .dst_regwen_o (core_duty_cycle_regwen),
      .dst_wd_o     (core_duty_cycle_wdata)
    );
    assign unused_core_duty_cycle_wdata =
        ^core_duty_cycle_wdata;

    logic duty_cycle_qe;
    logic [1:0] duty_cycle_flds_we;
    prim_flop #(
      .Width(1),
      .ResetValue(0)
    ) u_duty_cycle_qe (
      .clk_i(clk_core_i),
      .rst_ni(rst_core_ni),
      .d_i(&duty_cycle_flds_we),
      .q_o(duty_cycle_qe)
    );
    // Create REGWEN-gated WE signal
    logic core_duty_cycle_gated_we;
    assign core_duty_cycle_gated_we = core_duty_cycle_we & core_duty_cycle_regwen;
    //   F[a]: 15:0
    prim_subreg #(
      .DW      (16),
      .SwAccess(prim_subreg_pkg::SwAccessRW),
      .RESVAL  (16'h7fff),
      .Mubi    (1'b0)
    ) u_duty_cycle_a (
      .clk_i   (clk_core_i),
      .rst_ni  (rst_core_ni),

      // from register interface
      .we     (core_duty_cycle_gated_we),
      .wd     (core_duty_cycle_wdata[15:0]),

      // from internal hardware
      .de     (1'b0),
      .d      ('0),

      // to internal hardware
      .qe     (duty_cycle_flds_we[0]),
      .q      (reg2hw_duty_cycle_o[i].a.q),
      .ds     (),

      // to register interface (read)
      .qs     (core_duty_cycle_a_qs_int)
    );
    assign reg2hw_duty_cycle_o[i].a.qe = duty_cycle_qe;

    //   F[b]: 31:16
    prim_subreg #(
      .DW      (16),
      .SwAccess(prim_subreg_pkg::SwAccessRW),
      .RESVAL  (16'h7fff),
      .Mubi    (1'b0)
    ) u_duty_cycle_b (
      .clk_i   (clk_core_i),
      .rst_ni  (rst_core_ni),

      // from register interface
      .we     (core_duty_cycle_gated_we),
      .wd     (core_duty_cycle_wdata[31:16]),

      // from internal hardware
      .de     (1'b0),
      .d      ('0),

      // to internal hardware
      .qe     (duty_cycle_flds_we[1]),
      .q      (reg2hw_duty_cycle_o[i].b.q),
      .ds     (),

      // to register interface (read)
      .qs     (core_duty_cycle_b_qs_int)
    );
    assign reg2hw_duty_cycle_o[i].b.qe = duty_cycle_qe;
  end

  // R[blink_param_i]: V(False)
  for (genvar i = 0; i < NOutputs; i++) begin : gen_blink_param
    logic [15:0] core_blink_param_x_qs_int;
    logic [15:0] core_blink_param_y_qs_int;
    logic [31:0] core_blink_param_qs;
    logic [31:0] core_blink_param_wdata;
    logic core_blink_param_we;
    logic unused_core_blink_param_wdata;
    logic core_blink_param_regwen;

    always_comb begin
      core_blink_param_qs = 32'h0;
      core_blink_param_qs[15:0] = core_blink_param_x_qs_int;
      core_blink_param_qs[31:16] = core_blink_param_y_qs_int;
    end

    prim_reg_cdc #(
      .DataWidth(32),
      .ResetVal(32'h0),
      .BitMask(32'hffffffff),
      .DstWrReq(0)
    ) u_blink_param_cdc (
      .clk_src_i    (clk_i),
      .rst_src_ni   (rst_ni),
      .clk_dst_i    (clk_core_i),
      .rst_dst_ni   (rst_core_ni),
      .src_regwen_i (regwen_qs),
      .src_we_i     (blink_param_we[i]),
      .src_re_i     ('0),
      .src_wd_i     (reg_wdata[31:0]),
      .src_busy_o   (blink_param_busy[i]),
      .src_qs_o     (blink_param_qs[i]), // for software read back
      .dst_update_i ('0),
      .dst_ds_i     ('0),
      .dst_qs_i     (core_blink_param_qs),
      .dst_we_o     (core_blink_param_we),
      .dst_re_o     (),
      .dst_regwen_o (core_blink_param_regwen),
      .dst_wd_o     (core_blink_param_wdata)
    );
    assign unused_core_blink_param_wdata =
        ^core_blink_param_wdata;

    logic blink_param_qe;
    logic [1:0] blink_param_flds_we;
    prim_flop #(
      .Width(1),
      .ResetValue(0)
    ) u_blink_param_qe (
      .clk_i(clk_core_i),
      .rst_ni(rst_core_ni),
      .d_i(&blink_param_flds_we),
      .q_o(blink_param_qe)
    );
    // Create REGWEN-gated WE signal
    logic core_blink_param_gated_we;
    assign core_blink_param_gated_we = core_blink_param_we & core_blink_param_regwen;
    //   F[x]: 15:0
    prim_subreg #(
      .DW      (16),
      .SwAccess(prim_subreg_pkg::SwAccessRW),
      .RESVAL  (16'h0),
      .Mubi    (1'b0)
    ) u_blink_param_x (
      .clk_i   (clk_core_i),
      .rst_ni  (rst_core_ni),

      // from register interface
      .we     (core_blink_param_gated_we),
      .wd     (core_blink_param_wdata[15:0]),

      // from internal hardware
      .de     (1'b0),
      .d      ('0),

      // to internal hardware
      .qe     (blink_param_flds_we[0]),
      .q      (reg2hw_blink_param_o[i].x.q),
      .ds     (),

      // to register interface (read)
      .qs     (core_blink_param_x_qs_int)
    );
    assign reg2hw_blink_param_o[i].x.qe = blink_param_qe;

    //   F[y]: 31:16
    prim_subreg #(
      .DW      (16),
      .SwAccess(prim_subreg_pkg::SwAccessRW),
      .RESVAL  (16'h0),
      .Mubi    (1'b0)
    ) u_blink_param_y (
      .clk_i   (clk_core_i),
      .rst_ni  (rst_core_ni),

      // from register interface
      .we     (core_blink_param_gated_we),
      .wd     (core_blink_param_wdata[31:16]),

      // from internal hardware
      .de     (1'b0),
      .d      ('0),

      // to internal hardware
      .qe     (blink_param_flds_we[1]),
      .q      (reg2hw_blink_param_o[i].y.q),
      .ds     (),

      // to register interface (read)
      .qs     (core_blink_param_y_qs_int)
    );
    assign reg2hw_blink_param_o[i].y.qe = blink_param_qe;
  end


  logic [NumRegs-1:0] addr_hit;
  top_racl_pkg::racl_role_vec_t racl_role_vec;
  top_racl_pkg::racl_role_t racl_role;

  logic [NumRegs-1:0] racl_addr_hit_read;
  logic [NumRegs-1:0] racl_addr_hit_write;

  if (EnableRacl) begin : gen_racl_role_logic
    // Retrieve RACL role from user bits and one-hot encode that for the comparison bitmap
    assign racl_role = top_racl_pkg::tlul_extract_racl_role_bits(tl_i.a_user.rsvd);

    prim_onehot_enc #(
      .OneHotWidth( $bits(top_racl_pkg::racl_role_vec_t) )
    ) u_racl_role_encode (
      .in_i ( racl_role     ),
      .en_i ( 1'b1          ),
      .out_o( racl_role_vec )
    );
  end else begin : gen_no_racl_role_logic
    assign racl_role     = '0;
    assign racl_role_vec = '0;
  end

  always_comb begin
    racl_addr_hit_read  = '0;
    racl_addr_hit_write = '0;
    addr_hit[0] = (reg_addr == PWM_ALERT_TEST_OFFSET);
    addr_hit[1] = (reg_addr == PWM_REGWEN_OFFSET);
    addr_hit[2] = (reg_addr == PWM_CFG_OFFSET);
    addr_hit[3] = (reg_addr == PWM_PWM_EN_OFFSET);
    addr_hit[4] = (reg_addr == PWM_INVERT_OFFSET);
    for (int unsigned i = 0; i < NOutputs; i++) begin
      addr_hit[PwmParamIdx + i] =
          (reg_addr == AW'(pwm_pwm_param_offset() + 4 * i));
      addr_hit[DutyCycleIdx + i] =
          (reg_addr == AW'(pwm_duty_cycle_offset(NOutputs) + 4 * i));
      addr_hit[BlinkParamIdx + i] =
          (reg_addr == AW'(pwm_blink_param_offset(NOutputs) + 4 * i));
    end

    if (EnableRacl) begin : gen_racl_hit
      for (int unsigned slice_idx = 0; slice_idx < NumRegs; slice_idx++) begin
        racl_addr_hit_read[slice_idx] =
            addr_hit[slice_idx] & (|(racl_policies_i[RaclPolicySelVec[slice_idx]].read_perm
                                      & racl_role_vec));
        racl_addr_hit_write[slice_idx] =
            addr_hit[slice_idx] & (|(racl_policies_i[RaclPolicySelVec[slice_idx]].write_perm
                                      & racl_role_vec));
      end
    end else begin : gen_no_racl
      racl_addr_hit_read  = addr_hit;
      racl_addr_hit_write = addr_hit;
    end
  end


  assign addrmiss = (reg_re || reg_we) ? ~|addr_hit : 1'b0 ;
  // A valid address hit, access, but failed the RACL check
  assign racl_error_o.valid = |addr_hit & ((reg_re & ~|racl_addr_hit_read) |
                                           (reg_we & ~|racl_addr_hit_write));
  assign racl_error_o.request_address = top_pkg::TL_AW'(reg_addr);
  assign racl_error_o.racl_role       = racl_role;
  assign racl_error_o.overflow        = 1'b0;

  if (EnableRacl) begin : gen_racl_log
    assign racl_error_o.ctn_uid     = top_racl_pkg::tlul_extract_ctn_uid_bits(tl_i.a_user.rsvd);
    assign racl_error_o.read_access = tl_i.a_opcode == tlul_pkg::Get;
  end else begin : gen_no_racl_log
    assign racl_error_o.ctn_uid     = '0;
    assign racl_error_o.read_access = 1'b0;
  end

  // Check sub-word write is permitted
  always_comb begin
    wr_err = (reg_we &
              ((racl_addr_hit_write[0] & (|(4'b0001 & ~reg_be))) |
               (racl_addr_hit_write[1] & (|(4'b0001 & ~reg_be))) |
               (racl_addr_hit_write[2] & (|(4'b1111 & ~reg_be))) |
               (racl_addr_hit_write[3] & (|(ChanBitsPermit & ~reg_be))) |
               (racl_addr_hit_write[4] & (|(ChanBitsPermit & ~reg_be)))));
    for (int unsigned i = PwmParamIdx; i < NumRegs; i++) begin
      wr_err |= (reg_we & racl_addr_hit_write[i] & (|(4'b1111 & ~reg_be)));
    end
  end

  // Generate write-enables
  assign alert_test_we = racl_addr_hit_write[0] & reg_we & !reg_error;

  assign alert_test_wd = reg_wdata[0];
  assign regwen_we = racl_addr_hit_write[1] & reg_we & !reg_error;

  assign regwen_wd = reg_wdata[0];
  assign cfg_we = racl_addr_hit_write[2] & reg_we & !reg_error;

  assign pwm_en_we = racl_addr_hit_write[3] & reg_we & !reg_error;

  assign invert_we = racl_addr_hit_write[4] & reg_we & !reg_error;

  for (genvar i = 0; i < NOutputs; i++) begin : gen_chan_we
    assign pwm_param_we[i] = racl_addr_hit_write[PwmParamIdx + i] & reg_we & !reg_error;
    assign duty_cycle_we[i] = racl_addr_hit_write[DutyCycleIdx + i] & reg_we & !reg_error;
    assign blink_param_we[i] = racl_addr_hit_write[BlinkParamIdx + i] & reg_we & !reg_error;
  end

  // Assign write-enables to checker logic vector.
  always_comb begin
    reg_we_check[0] = alert_test_we;
    reg_we_check[1] = regwen_we;
    reg_we_check[2] = cfg_we;
    reg_we_check[3] = pwm_en_we;
    reg_we_check[4] = invert_we;
    for (int unsigned i = 0; i < NOutputs; i++) begin
      reg_we_check[PwmParamIdx + i] = pwm_param_we[i];
      reg_we_check[DutyCycleIdx + i] = duty_cycle_we[i];
      reg_we_check[BlinkParamIdx + i] = blink_param_we[i];
    end
  end

  // Read data return
  logic [DW-1:0] chan_rdata;
  always_comb begin
    chan_rdata = '0;
    for (int unsigned i = 0; i < NOutputs; i++) begin
      if (racl_addr_hit_read[PwmParamIdx + i]) chan_rdata = DW'(pwm_param_qs[i]);
      if (racl_addr_hit_read[DutyCycleIdx + i]) chan_rdata = DW'(duty_cycle_qs[i]);
      if (racl_addr_hit_read[BlinkParamIdx + i]) chan_rdata = DW'(blink_param_qs[i]);
    end
  end

  always_comb begin
    reg_rdata_next = '0;
    unique case (1'b1)
      racl_addr_hit_read[0]: begin
        reg_rdata_next[0] = '0;
      end

      racl_addr_hit_read[1]: begin
        reg_rdata_next[0] = regwen_qs;
      end

      racl_addr_hit_read[2]: begin
        reg_rdata_next = DW'(cfg_qs);
      end
      racl_addr_hit_read[3]: begin
        reg_rdata_next = DW'(pwm_en_qs);
      end
      racl_addr_hit_read[4]: begin
        reg_rdata_next = DW'(invert_qs);
      end
      |racl_addr_hit_read[NumRegs-1:PwmParamIdx]: begin
        reg_rdata_next = chan_rdata;
      end
      default: begin
        reg_rdata_next = '1;
      end
    endcase
  end

  // shadow busy
  logic shadow_busy;
  assign shadow_busy = 1'b0;

  // register busy
  logic chan_busy;
  always_comb begin
    chan_busy = 1'b0;
    for (int unsigned i = 0; i < NOutputs; i++) begin
      if (addr_hit[PwmParamIdx + i]) chan_busy = pwm_param_busy[i];
      if (addr_hit[DutyCycleIdx + i]) chan_busy = duty_cycle_busy[i];
      if (addr_hit[BlinkParamIdx + i]) chan_busy = blink_param_busy[i];
    end
  end

  logic reg_busy_sel;
  assign reg_busy = (reg_busy_sel | shadow_busy) & tl_i.a_valid;
  always_comb begin
    reg_busy_sel = '0;
    unique case (1'b1)
      addr_hit[2]: begin
        reg_busy_sel = cfg_busy;
      end
      addr_hit[3]: begin
        reg_busy_sel = pwm_en_busy;
      end
      addr_hit[4]: begin
        reg_busy_sel = invert_busy;
      end
      |addr_hit[NumRegs-1:PwmParamIdx]: begin
        reg_busy_sel = chan_busy;
      end
      default: begin
        reg_busy_sel  = '0;
      end
    endcase
  end


  // Unused signal tieoff

  // wdata / byte enable are not always fully used
  // add a blanket unused statement to handle lint waivers
  logic unused_wdata;
  logic unused_be;
  assign unused_wdata = ^reg_wdata;
  assign unused_be = ^reg_be;
  logic unused_policy_sel;
  assign unused_policy_sel = ^racl_policies_i;

  // Assertions for Register Interface
  `OCAH_OT_ASSERT_PULSE(wePulse, reg_we, clk_i, !rst_ni)
  `OCAH_OT_ASSERT_PULSE(rePulse, reg_re, clk_i, !rst_ni)

  `OCAH_OT_ASSERT(reAfterRv, $rose(reg_re || reg_we) |=> tl_o_pre.d_valid, clk_i, !rst_ni)

  `OCAH_OT_ASSERT(en2addrHit, (reg_we || reg_re) |-> $onehot0(addr_hit), clk_i, !rst_ni)

  // this is formulated as an assumption such that the FPV testbenches do disprove this
  // property by mistake
  //`OCAH_OT_ASSUME(reqParity, tl_reg_h2d.a_valid |-> tl_reg_h2d.a_user.chk_en == tlul_pkg::CheckDis)

endmodule
