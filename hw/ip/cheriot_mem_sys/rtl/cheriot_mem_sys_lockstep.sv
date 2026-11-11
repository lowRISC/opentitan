// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

// CHERIoT memory subsystem lockstep module
// This module instantiates a second copy of cheriot_mem_sys_core, and compares its outputs against
// those from the main copy. The second copy runs synchronously with the main copy, delayed by
// LockstepOffset cycles. Every port of the main copy is an input here: its inputs are delayed into
// the second copy, its outputs are compared.

// SEC_CM: LOGIC.SHADOW
module cheriot_mem_sys_lockstep
  import cheriot_mem_sys_reg_pkg::*;
#(
  // Cycles the second copy runs behind the main copy
  parameter int unsigned LockstepOffset   = 1,
  // TL-UL address type
  parameter type         addr_t           = logic [top_pkg::TL_AW-1:0],
  // Top-level address map parameters
  parameter addr_t       MainSramBaseAddr = 'h1000_0000,
  parameter addr_t       MainSramTopAddr  = 'h1003_0000,
  parameter addr_t       NvmBaseAddr      = 'h3000_0000,
  parameter addr_t       NvmTopAddr       = 'h3020_0000,
  parameter addr_t       MetaSramBaseAddr = 'h1100_0000,
  parameter int unsigned MemSizeRevbm     = 3072
) (
  input  logic clk_i,
  input  logic rst_ni,

  // Scan mode, bypasses the reset of the second copy
  input  prim_mubi_pkg::mubi4_t scanmode_i,
  input  logic                  scan_rst_ni,

  // CHERIoT mode enabled
  input  prim_mubi_pkg::mubi4_t cheriot_ena_i,

  // Revocation engine registers
  input  cheriot_mem_sys_reg2hw_tbre_base_addr_reg_t tbre_base_addr_i,
  input  cheriot_mem_sys_reg2hw_tbre_num_caps_reg_t  tbre_num_caps_i,
  input  cheriot_mem_sys_reg2hw_tbre_start_reg_t     tbre_start_i,
  input  cheriot_mem_sys_hw2reg_tbre_regwen_reg_t    tbre_regwen_i,
  input  cheriot_mem_sys_hw2reg_tbre_status_reg_t    tbre_status_i,
  input  cheriot_mem_sys_hw2reg_tbre_epoch_reg_t     tbre_epoch_i,

  // Revocation engine done event
  input  logic tbre_done_i,

  // Fatal alert request: an output mismatch or a fatal error of the second copy
  output logic alert_fatal_fault_o,

  // Core data input port
  input  tlul_pkg::tl_h2d_t     cored_tl_d_h2d_i,
  input  prim_mubi_pkg::mubi4_t cored_tag_h2d_i,
  input  tlul_pkg::tl_d2h_t     cored_tl_d_d2h_i,
  input  prim_mubi_pkg::mubi4_t cored_tag_d2h_i,

  // TRVK revocation bitmap input port
  input  tlul_pkg::tl_h2d_t corerevbm_tl_h2d_i,
  input  tlul_pkg::tl_d2h_t corerevbm_tl_d2h_i,

  // System revocation bitmap port
  input  tlul_pkg::tl_h2d_t revbm_tl_d_h2d_i,
  input  tlul_pkg::tl_d2h_t revbm_tl_d_d2h_i,

  // Core data output port towards interconnect
  input  tlul_pkg::tl_h2d_t cored_tl_h_h2d_i,
  input  tlul_pkg::tl_d2h_t cored_tl_h_d2h_i,

  // Revocation engine read-only port towards interconnect
  input  tlul_pkg::tl_h2d_t tbre_tl_h_h2d_i,
  input  tlul_pkg::tl_d2h_t tbre_tl_h_d2h_i,

  // Meta SRAM host port (to external sram_ctrl)
  input  tlul_pkg::tl_h2d_t meta_sram_tl_h2d_i,
  input  tlul_pkg::tl_d2h_t meta_sram_tl_d2h_i
);

  localparam int unsigned LockstepOffsetW = prim_util_pkg::vbits(LockstepOffset);
  // Main copy outputs are delayed for an extra cycle due to the second copy's output registers
  localparam int unsigned OutputsOffset = LockstepOffset + 1;

  `ASSERT_INIT(LockstepOffsetMin_A, LockstepOffset >= 1)

  //////////////////////
  // Reset generation //
  //////////////////////

  // MuBi4 values, plain vectors like the prim_flop ports they pass through
  logic                                 rst_shadow_cnt_err;
  logic [prim_mubi_pkg::MuBi4Width-1:0] rst_shadow_set_d, rst_shadow_set_q;
  logic                                 rst_shadow_n;
  logic [prim_mubi_pkg::MuBi4Width-1:0] enable_cmp_d, enable_cmp_q;

  if (LockstepOffset > 1) begin : gen_reset_counter
    // Upon reset, the comparison is stopped and the second copy is reset, both immediately. A
    // counter is started, and after LockstepOffset clock cycles the reset of the second copy is
    // synchronously released. The comparison is started in the following clock cycle.

    logic [LockstepOffsetW-1:0] rst_shadow_cnt;

    // Counts up after a reset and saturates at its maximum, which is at least LockstepOffset - 1.
    prim_count #(
      .Width          (LockstepOffsetW),
      .ResetValue     (LockstepOffsetW'(1'b0)),
      .PossibleActions(prim_count_pkg::Incr)
    ) u_rst_shadow_cnt (
      .clk_i,
      .rst_ni,
      .clr_i             (1'b0),
      .set_i             (1'b0),
      .set_cnt_i         ('0),
      .incr_en_i         (1'b1),
      .decr_en_i         (1'b0),
      .step_i            (LockstepOffsetW'(1'b1)),
      .commit_i          (1'b1),
      .cnt_o             (rst_shadow_cnt),
      .cnt_after_commit_o(),
      .err_o             (rst_shadow_cnt_err)
    );

    assign rst_shadow_set_d = (rst_shadow_cnt >= LockstepOffsetW'(LockstepOffset - 1)) ?
                              prim_mubi_pkg::MuBi4True : prim_mubi_pkg::MuBi4False;

    assign enable_cmp_d = rst_shadow_set_q;

  end else begin : gen_no_reset_counter
    // The reset of the second copy is released at the first clock edge out of reset, the
    // comparison starts one cycle later.
    assign rst_shadow_set_d = prim_mubi_pkg::MuBi4True;

    // There is no counter that could fail.
    assign rst_shadow_cnt_err = 1'b0;

    always_ff @(posedge clk_i or negedge rst_ni) begin : proc_enable_cmp_delay
      if (!rst_ni) begin
        enable_cmp_d <= prim_mubi_pkg::MuBi4False;
      end else begin
        enable_cmp_d <= prim_mubi_pkg::MuBi4True;
      end
    end

    // Only the reset bit of rst_shadow_set_q is used.
    logic [2:0] unused_rst_shadow_set_q;
    assign unused_rst_shadow_set_q = {rst_shadow_set_q[3:2], rst_shadow_set_q[0]};
  end

  // The primitives below are used to place size-only constraints in order to prevent synthesis
  // optimizations and preserve anchor points for constraining backend tools.
  prim_flop #(
    .Width     (prim_mubi_pkg::MuBi4Width),
    .ResetValue(prim_mubi_pkg::MuBi4Width'(prim_mubi_pkg::MuBi4False))
  ) u_prim_rst_shadow_set_flop (
    .clk_i,
    .rst_ni,
    .d_i(rst_shadow_set_d),
    .q_o(rst_shadow_set_q)
  );

  prim_flop #(
    .Width     (prim_mubi_pkg::MuBi4Width),
    .ResetValue(prim_mubi_pkg::MuBi4Width'(prim_mubi_pkg::MuBi4False))
  ) u_prim_enable_cmp_flop (
    .clk_i,
    .rst_ni,
    .d_i(enable_cmp_d),
    .q_o(enable_cmp_q)
  );

  // Bit 1 is set in MuBi4True only, so it releases the reset of the second copy from a single flop.
  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_prim_rst_shadow_n_mux2 (
    .clk0_i(rst_shadow_set_q[1]),
    .clk1_i(scan_rst_ni),
    .sel_i (prim_mubi_pkg::mubi4_test_true_strict(scanmode_i)),
    .clk_o (rst_shadow_n)
  );

  `ASSERT_INIT(RstShadowSetBit_A, (prim_mubi_pkg::MuBi4True & 4'b0010) == 4'b0010 &&
                                  (prim_mubi_pkg::MuBi4False & 4'b0010) == 4'b0000)

  //////////////////
  // Input delays //
  //////////////////

  typedef struct packed {
    prim_mubi_pkg::mubi4_t                      cheriot_ena;
    cheriot_mem_sys_reg2hw_tbre_base_addr_reg_t tbre_base_addr;
    cheriot_mem_sys_reg2hw_tbre_num_caps_reg_t  tbre_num_caps;
    cheriot_mem_sys_reg2hw_tbre_start_reg_t     tbre_start;
    tlul_pkg::tl_h2d_t                          cored_tl_d;
    prim_mubi_pkg::mubi4_t                      cored_tag_h2d;
    tlul_pkg::tl_h2d_t                          corerevbm_tl;
    tlul_pkg::tl_h2d_t                          revbm_tl_d;
    tlul_pkg::tl_d2h_t                          cored_tl_h;
    tlul_pkg::tl_d2h_t                          tbre_tl_h;
    tlul_pkg::tl_d2h_t                          meta_sram_tl;
  } delayed_inputs_t;

  // Stage LockstepOffset-1 takes the inputs of the main copy, stage 0 feeds the second copy.
  delayed_inputs_t                      shadow_inputs_in;
  delayed_inputs_t [LockstepOffset-1:0] shadow_inputs_d, shadow_inputs_q;

  if (LockstepOffset > 1) begin : gen_multi_cycle_delay
    assign shadow_inputs_d = {shadow_inputs_in, shadow_inputs_q[LockstepOffset-1:1]};
  end else begin : gen_single_cycle_delay
    assign shadow_inputs_d[0] = shadow_inputs_in;
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_shadow_inputs_store
    if (!rst_ni) begin
      shadow_inputs_q <= '0;
    end else begin
      shadow_inputs_q <= shadow_inputs_d;
    end
  end

  // Assign the inputs to the delay structure
  assign shadow_inputs_in.cheriot_ena    = cheriot_ena_i;
  assign shadow_inputs_in.tbre_base_addr = tbre_base_addr_i;
  assign shadow_inputs_in.tbre_num_caps  = tbre_num_caps_i;
  assign shadow_inputs_in.tbre_start     = tbre_start_i;
  assign shadow_inputs_in.cored_tl_d     = cored_tl_d_h2d_i;
  assign shadow_inputs_in.cored_tag_h2d  = cored_tag_h2d_i;
  assign shadow_inputs_in.corerevbm_tl   = corerevbm_tl_h2d_i;
  assign shadow_inputs_in.revbm_tl_d     = revbm_tl_d_h2d_i;
  assign shadow_inputs_in.cored_tl_h     = cored_tl_h_d2h_i;
  assign shadow_inputs_in.tbre_tl_h      = tbre_tl_h_d2h_i;
  assign shadow_inputs_in.meta_sram_tl   = meta_sram_tl_d2h_i;

  ///////////////////
  // Output delays //
  ///////////////////

  typedef struct packed {
    cheriot_mem_sys_hw2reg_tbre_regwen_reg_t tbre_regwen;
    cheriot_mem_sys_hw2reg_tbre_status_reg_t tbre_status;
    cheriot_mem_sys_hw2reg_tbre_epoch_reg_t  tbre_epoch;
    logic                                    tbre_done;
    tlul_pkg::tl_d2h_t                       cored_tl_d;
    prim_mubi_pkg::mubi4_t                   cored_tag_d2h;
    tlul_pkg::tl_d2h_t                       corerevbm_tl;
    tlul_pkg::tl_d2h_t                       revbm_tl_d;
    tlul_pkg::tl_h2d_t                       cored_tl_h;
    tlul_pkg::tl_h2d_t                       tbre_tl_h;
    tlul_pkg::tl_h2d_t                       meta_sram_tl;
  } delayed_outputs_t;

  // Stage OutputsOffset-1 takes the outputs of the main copy, stage 0 is compared.
  delayed_outputs_t                     core_outputs_in;
  delayed_outputs_t [OutputsOffset-1:0] core_outputs_d, core_outputs_q;
  delayed_outputs_t                     shadow_outputs_d, shadow_outputs_q;

  // Assign the outputs of the main copy to the structure
  assign core_outputs_in.tbre_regwen   = tbre_regwen_i;
  assign core_outputs_in.tbre_status   = tbre_status_i;
  assign core_outputs_in.tbre_epoch    = tbre_epoch_i;
  assign core_outputs_in.tbre_done     = tbre_done_i;
  assign core_outputs_in.cored_tl_d    = cored_tl_d_d2h_i;
  assign core_outputs_in.cored_tag_d2h = cored_tag_d2h_i;
  assign core_outputs_in.corerevbm_tl  = corerevbm_tl_d2h_i;
  assign core_outputs_in.revbm_tl_d    = revbm_tl_d_d2h_i;
  assign core_outputs_in.cored_tl_h    = cored_tl_h_h2d_i;
  assign core_outputs_in.tbre_tl_h     = tbre_tl_h_h2d_i;
  assign core_outputs_in.meta_sram_tl  = meta_sram_tl_h2d_i;

  // OutputsOffset is at least 2.
  assign core_outputs_d = {core_outputs_in, core_outputs_q[OutputsOffset-1:1]};

  // No reset: the comparison only starts once both delay lines hold outputs from after the reset.
  always_ff @(posedge clk_i) begin : proc_core_outputs_store
    core_outputs_q <= core_outputs_d;
  end

  // Register the outputs of the second copy
  always_ff @(posedge clk_i) begin : proc_shadow_outputs_store
    shadow_outputs_q <= shadow_outputs_d;
  end

  /////////////////
  // Second copy //
  /////////////////

  logic shadow_alert_fatal_fault;

  cheriot_mem_sys_core #(
    .addr_t          (addr_t),
    .MainSramBaseAddr(MainSramBaseAddr),
    .MainSramTopAddr (MainSramTopAddr),
    .NvmBaseAddr     (NvmBaseAddr),
    .NvmTopAddr      (NvmTopAddr),
    .MetaSramBaseAddr(MetaSramBaseAddr),
    .MemSizeRevbm    (MemSizeRevbm)
  ) u_cheriot_mem_sys_core_shadow (
    .clk_i,
    .rst_ni             (rst_shadow_n),
    .cheriot_ena_i      (shadow_inputs_q[0].cheriot_ena),
    .tbre_base_addr_i   (shadow_inputs_q[0].tbre_base_addr),
    .tbre_num_caps_i    (shadow_inputs_q[0].tbre_num_caps),
    .tbre_start_i       (shadow_inputs_q[0].tbre_start),
    .tbre_regwen_o      (shadow_outputs_d.tbre_regwen),
    .tbre_status_o      (shadow_outputs_d.tbre_status),
    .tbre_epoch_o       (shadow_outputs_d.tbre_epoch),
    .tbre_done_o        (shadow_outputs_d.tbre_done),
    .alert_fatal_fault_o(shadow_alert_fatal_fault),
    .cored_tl_d_i       (shadow_inputs_q[0].cored_tl_d),
    .cored_tag_h2d_i    (shadow_inputs_q[0].cored_tag_h2d),
    .cored_tl_d_o       (shadow_outputs_d.cored_tl_d),
    .cored_tag_d2h_o    (shadow_outputs_d.cored_tag_d2h),
    .corerevbm_tl_i     (shadow_inputs_q[0].corerevbm_tl),
    .corerevbm_tl_o     (shadow_outputs_d.corerevbm_tl),
    .revbm_tl_d_i       (shadow_inputs_q[0].revbm_tl_d),
    .revbm_tl_d_o       (shadow_outputs_d.revbm_tl_d),
    .cored_tl_h_o       (shadow_outputs_d.cored_tl_h),
    .cored_tl_h_i       (shadow_inputs_q[0].cored_tl_h),
    .tbre_tl_h_o        (shadow_outputs_d.tbre_tl_h),
    .tbre_tl_h_i        (shadow_inputs_q[0].tbre_tl_h),
    .meta_sram_tl_o     (shadow_outputs_d.meta_sram_tl),
    .meta_sram_tl_i     (shadow_inputs_q[0].meta_sram_tl)
  );

  /////////////////////////
  // Compare the outputs //
  /////////////////////////

  logic outputs_mismatch;

  // Any value except MuBi4False turns on the comparison. All output bits are compared, including
  // the payload of TL-UL channels that are not valid.
  assign outputs_mismatch =
      prim_mubi_pkg::mubi4_test_true_loose(prim_mubi_pkg::mubi4_t'(enable_cmp_q)) &&
      (shadow_outputs_q != core_outputs_q[0]);

  assign alert_fatal_fault_o = outputs_mismatch || shadow_alert_fatal_fault || rst_shadow_cnt_err;

endmodule
