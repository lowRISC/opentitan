// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module pinmux_strap_sampling
  import pinmux_pkg::*;
  import pinmux_reg_pkg::*;
(
  input                            clk_i,
  input                            rst_ni,
  // MIO inputs.
  // TODO(#5221): need tapped IOs for JTAG mux.
  input  logic [NMioPads-1:0]      mio_in_i,
  // Used for TAP qualification
  input  logic                     strap_en_i,
  input  lc_ctrl_pkg::lc_tx_t      lc_dft_en_i,
  input  lc_ctrl_pkg::lc_tx_t      lc_hw_debug_en_i,
  // Sampled values for DFT straps
  output dft_strap_test_req_t      dft_strap_test_o,
  // Qualified JTAG signals for TAPs
  output jtag_pkg::jtag_req_t      lc_jtag_o,
  input  jtag_pkg::jtag_rsp_t      lc_jtag_i,
  output jtag_pkg::jtag_req_t      rv_jtag_o,
  input  jtag_pkg::jtag_rsp_t      rv_jtag_i,
  output jtag_pkg::jtag_req_t      dft_jtag_o,
  input  jtag_pkg::jtag_rsp_t      dft_jtag_i
);

  /////////////////////////////////////
  // Life cycle signal synchronizers //
  /////////////////////////////////////

  lc_ctrl_pkg::lc_tx_t [1:0] lc_hw_debug_en;
  lc_ctrl_pkg::lc_tx_t [1:0] lc_dft_en;
  prim_lc_sync #(
    .NumCopies(2)
  ) u_prim_lc_sync_rv (
    .clk_i,
    .rst_ni,
    .lc_en_i(lc_hw_debug_en_i),
    .lc_en_o(lc_hw_debug_en)
  );
  prim_lc_sync #(
    .NumCopies(2)
  ) u_prim_lc_sync_dft (
    .clk_i,
    .rst_ni,
    .lc_en_i(lc_dft_en_i),
    .lc_en_o(lc_dft_en)
  );

  //////////////////////////
  // Strap Sampling Logic //
  //////////////////////////

  typedef enum logic [NTapStraps-1:0] {
    FuncSel   = 2'b00,
    LcTapSel  = 2'b01,
    RvTapSel  = 2'b10,
    DftTapSel = 2'b11
  } tap_strap_t;

  logic strap_en_q;
  logic dft_strap_valid_d, dft_strap_valid_q;
  logic lc_strap_sample_en, rv_strap_sample_en, dft_strap_sample_en;
  logic [1:0] tap_strap_sample_en;
  logic [NTapStraps-1:0] tap_strap_d, tap_strap_q;
  logic [NDFTStraps-1:0] dft_strap_d, dft_strap_q;
  lc_ctrl_pkg::lc_tx_e continue_sampling_d, continue_sampling_q;

  // Not all MIOs are used.
  logic unused_mio_in;
  assign unused_mio_in = ^mio_in_i;

  // The LC strap at index 0 has a slightly different
  // enable condition than the DFT strap at index 1.
  for (genvar k = 0; k < NTapStraps; k++) begin : gen_lc_strap_taps
    assign tap_strap_d[k] = (tap_strap_sample_en[k]) ? mio_in_i[TapStrapPos[k]] : tap_strap_q[k];
  end

  // We're always using the DFT strap sample enable for the DFT straps.
  for (genvar k = 0; k < NDFTStraps; k++) begin : gen_dft_strap_taps
    assign dft_strap_d[k] = (dft_strap_sample_en) ? mio_in_i[DftStrapPos[k]] : dft_strap_q[k];
  end

  assign dft_strap_valid_d = dft_strap_sample_en | dft_strap_valid_q;
  assign dft_strap_test_o.valid  = dft_strap_valid_q;
  assign dft_strap_test_o.straps = dft_strap_q;

  assign tap_strap_sample_en = {rv_strap_sample_en,
                                lc_strap_sample_en};

  always_comb begin : p_strap_sampling
    lc_strap_sample_en = 1'b0;
    rv_strap_sample_en = 1'b0;
    dft_strap_sample_en = 1'b0;
    continue_sampling_d = continue_sampling_q;

    // Initial strap sampling pulse from pwrmgr,
    // qualified by life cycle signals.
    if (strap_en_i || continue_sampling_q == lc_ctrl_pkg::On) begin
      lc_strap_sample_en = 1'b1;
      if (lc_hw_debug_en[0] == lc_ctrl_pkg::On) begin
        rv_strap_sample_en = 1'b1;
      end
      if (lc_dft_en[0] == lc_ctrl_pkg::On) begin
        dft_strap_sample_en = 1'b1;
      end
    end

    // In case DFT is enabled, and in case the TAP straps
    // where not set to functional mode upon the first
    // sampling event, we continue sampling all straps
    // until system reset. This is used during the
    // DFT-enabled life cycle states only.
    if (lc_dft_en[0] == lc_ctrl_pkg::On) begin
      if (strap_en_q &&
          tap_strap_t'(tap_strap_q) != FuncSel) begin
        continue_sampling_d = lc_ctrl_pkg::On;
      end
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_strap_sample
    if (!rst_ni) begin
      tap_strap_q         <= '0;
      dft_strap_q         <= '0;
      strap_en_q          <= 1'b0;
      dft_strap_valid_q   <= 1'b0;
      continue_sampling_q <= lc_ctrl_pkg::Off;
    end else begin
      tap_strap_q         <= tap_strap_d;
      dft_strap_q         <= dft_strap_d;
      strap_en_q          <= strap_en_i;
      dft_strap_valid_q   <= dft_strap_valid_d;
      continue_sampling_q <= continue_sampling_d;
    end
  end

  ////////////////////
  // TAP Selection  //
  ////////////////////

  jtag_pkg::jtag_req_t jtag_req, lc_jtag_req, rv_jtag_req, dft_jtag_req;
  jtag_pkg::jtag_rsp_t jtag_rsp, lc_jtag_rsp, rv_jtag_rsp, dft_jtag_rsp;

  // TODO(#5221): need to mux this with the correct MIOs.
  // But first, the jtag_mux from the chip level hierarchy needs
  // to be pulled into pinmux, and the FPGA emulation and the simulation
  // environments need to be adapted such that this does not break our
  // regressions.
  logic unused_jtag_rsp;
  assign jtag_req = '0;
  assign unused_jtag_rsp = ^jtag_rsp;

  // This muxes the JTAG signals to the correct TAP, based on the
  // sampled straps. Further, the individual JTAG signals are gated
  // using the corresponding life cycle signal.
  tap_strap_t tap_strap;
  assign tap_strap = tap_strap_t'(tap_strap_q);
  `ASSERT_KNOWN(TapStrapKnown_A, tap_strap)

  always_comb begin : p_tap_mux
    jtag_rsp     = '0;
    lc_jtag_req  = '0;
    rv_jtag_req  = '0;
    dft_jtag_req = '0;

    unique case (tap_strap)
      LcTapSel: begin
        lc_jtag_req = jtag_req;
        jtag_rsp = lc_jtag_rsp;
      end
      RvTapSel: begin
        if (lc_hw_debug_en[1] == lc_ctrl_pkg::On) begin
          rv_jtag_req = jtag_req;
          jtag_rsp = rv_jtag_rsp;
        end
      end
      DftTapSel: begin
        if (lc_dft_en[1] == lc_ctrl_pkg::On) begin
          dft_jtag_req = jtag_req;
          jtag_rsp = dft_jtag_rsp;
        end
      end
      default: ;
    endcase // tap_strap_t'(tap_strap_q)
  end

  // Insert hand instantiated buffers for
  // these signals to prevent further optimization.
  pinmux_jtag_buf u_pinmux_jtag_buf_lc (
    .req_i(lc_jtag_req),
    .req_o(lc_jtag_o),
    .rsp_i(lc_jtag_i),
    .rsp_o(lc_jtag_rsp)
  );
  pinmux_jtag_buf u_pinmux_jtag_buf_rv (
    .req_i(rv_jtag_req),
    .req_o(rv_jtag_o),
    .rsp_i(rv_jtag_i),
    .rsp_o(rv_jtag_rsp)
  );
  pinmux_jtag_buf u_pinmux_jtag_buf_dft (
    .req_i(dft_jtag_req),
    .req_o(dft_jtag_o),
    .rsp_i(dft_jtag_i),
    .rsp_o(dft_jtag_rsp)
  );

  ////////////////
  // Assertions //
  ////////////////

  // The strap sampling enable input shall be pulsed high exactly once after cold boot.
  `ASSERT(PwrMgrStrapSampleOnce_A, strap_en_i |=> ##0 !strap_en_i [*])

  `ASSERT(RvTapOff0_A, lc_hw_debug_en_i == lc_ctrl_pkg::Off |-> ##2 rv_jtag_o == '0)
  `ASSERT(RvTapOff1_A, lc_hw_debug_en_i == lc_ctrl_pkg::Off |-> ##2 rv_jtag_i == '0)
  `ASSERT(DftTapOff0_A, lc_dft_en_i == lc_ctrl_pkg::Off |-> ##2 dft_jtag_o == '0)
  `ASSERT(DftTapOff1_A, lc_dft_en_i == lc_ctrl_pkg::Off |-> ##2 dft_jtag_i == '0)

endmodule : pinmux_strap_sampling
