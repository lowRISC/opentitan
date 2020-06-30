// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// This it the padctrl portion that has to be placed into the toplevel.
// It basically just wraps the regfile and outputs the configuration bits
// to be consumed on the chiplevel.
//

`include "prim_assert.sv"

module padctrl import padctrl_reg_pkg::*; (
  input                                  clk_i,
  input                                  rst_ni,
  // Bus Interface (device)
  input  tlul_pkg::tl_h2d_t              tl_i,
  output tlul_pkg::tl_d2h_t              tl_o,
  // pad attributes to chip level instance
  output logic[NMioPads-1:0][AttrDw-1:0] mio_attr_o,
  output logic[NDioPads-1:0][AttrDw-1:0] dio_attr_o
);

  /////////////
  // Regfile //
  /////////////

  padctrl_reg2hw_t reg2hw;
  padctrl_hw2reg_t hw2reg;

  padctrl_reg_top u_reg (
    .clk_i  ,
    .rst_ni ,
    .tl_i   ,
    .tl_o   ,
    .reg2hw ,
    .hw2reg ,
    .devmode_i(1'b1)
  );

  ////////////////
  // HWEXT Regs //
  ////////////////

  logic [NDioPads-1:0][AttrDw-1:0] dio_attr_q;
  logic [NMioPads-1:0][AttrDw-1:0] mio_attr_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_regs
    if (!rst_ni) begin
      dio_attr_q <= '0;
      mio_attr_q <= '0;
    end else begin
      // dedicated pads
      for (int kk = 0; kk < NDioPads; kk++) begin
        if (reg2hw.dio_pads[kk].qe) begin
          dio_attr_q[kk] <= reg2hw.dio_pads[kk].q;
        end
      end
      // muxed pads
      for (int kk = 0; kk < NMioPads; kk++) begin
        if (reg2hw.mio_pads[kk].qe) begin
          mio_attr_q[kk] <= reg2hw.mio_pads[kk].q;
        end
      end
    end
  end

  ////////////////////////
  // Connect attributes //
  ////////////////////////

  // Note that these are not real pad instances. We only query the supported attributes here
  for (genvar k = 0; k < NDioPads; k++) begin : gen_dio_attr
    logic [AttrDw-1:0] warl_mask;

    prim_generic_pad_wrapper #(
      .AttrDw   ( AttrDw        ),
      .WarlOnly ( 1'b1          ) // this prevents instantiation of pad logic
    ) i_prim_generic_pad_wrapper (
      .inout_io (               ),
      .in_o     (               ),
      .ie_i     ( 1'b0          ),
      .out_i    ( 1'b0          ),
      .oe_i     ( 1'b0          ),
      .attr_i   ( '0            ),
      .warl_o   ( warl_mask     )
    );

    assign dio_attr_o[k]        = dio_attr_q[k] & warl_mask;
    assign hw2reg.dio_pads[k].d = dio_attr_q[k] & warl_mask;
  end

  for (genvar k = 0; k < NMioPads; k++) begin : gen_mio_attr
    logic [AttrDw-1:0] warl_mask;

    prim_generic_pad_wrapper #(
      .AttrDw   ( AttrDw        ),
      .WarlOnly ( 1'b1          ) // this prevents instantiation of pad logic
    ) i_prim_generic_pad_wrapper (
      .inout_io (               ),
      .in_o     (               ),
      .ie_i     ( 1'b0          ),
      .out_i    ( 1'b0          ),
      .oe_i     ( 1'b0          ),
      .attr_i   ( '0            ),
      .warl_o   ( warl_mask     )
    );

    assign mio_attr_o[k]        = mio_attr_q[k] & warl_mask;
    assign hw2reg.mio_pads[k].d = mio_attr_q[k] & warl_mask;
  end

  ////////////////
  // Assertions //
  ////////////////

  `ASSERT_KNOWN(TlDValidKnownO_A, tl_o.d_valid)
  `ASSERT_KNOWN(TlAReadyKnownO_A, tl_o.a_ready)
  `ASSERT_KNOWN(MioKnownO_A, mio_attr_o)
  `ASSERT_KNOWN(DioKnownO_A, dio_attr_o)

endmodule : padctrl
