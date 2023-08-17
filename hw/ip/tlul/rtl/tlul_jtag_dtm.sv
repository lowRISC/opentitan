// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// JTAG DTM to TL-UL Converter.
// This implements a JTAG DTM according to the RISC-V external debug v0.13 specification and
// uses the TL-UL protocol to transport read/write operations to the RISC-V debug module
// (i.e. the DMI is implemented with the TL-UL protocol):
// https://github.com/riscv/riscv-debug-spec/blob/release/riscv-debug-release.pdf
//

module tlul_jtag_dtm #(
  // Idcode value for the JTAG.
  parameter logic [31:0] IdcodeValue = 32'h00000001,
  parameter int unsigned NumDmiByteAbits = 18
) (
  input                                              clk_i,
  input                                              rst_ni,
  input  jtag_pkg::jtag_req_t                        jtag_i,
  output jtag_pkg::jtag_rsp_t                        jtag_o,
  // This bypasses the clock inverter inside the JTAG TAP for scanmmode.
  input                                              scan_rst_ni,
  input  prim_mubi_pkg::mubi4_t                      scanmode_i,
  // TL-UL-based DMI
  output tlul_pkg::tl_h2d_t                          tl_h2d_o,
  input  tlul_pkg::tl_d2h_t                          tl_d2h_i
);

  dm::dmi_req_t dmi_req;
  logic dmi_req_valid;
  logic dmi_req_ready;
  dm::dmi_resp_t dmi_resp;
  logic dmi_resp_ready;
  logic dmi_resp_valid;

  logic scanmode;
  prim_mubi4_dec u_prim_mubi4_dec (
    .mubi_i(scanmode_i),
    .mubi_dec_o(scanmode)
  );

  logic tck_muxed;
  logic trst_n_muxed;
  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_prim_clock_mux2 (
    .clk0_i(jtag_i.tck),
    .clk1_i(clk_i),
    .sel_i (scanmode),
    .clk_o (tck_muxed)
  );

  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_prim_rst_n_mux2 (
    .clk0_i(jtag_i.trst_n),
    .clk1_i(scan_rst_ni),
    .sel_i (scanmode),
    .clk_o (trst_n_muxed)
  );

  // TODO: At the moment, this uses the JTAG DTM implementation from the PULP project.
  // This module should be refactored in the future to support TL-UL directly, instead
  // of a custom DMI protocol which necessitates another translation layer to TL-UL.
  logic req_ready;
  assign req_ready = dmi_req_ready && dmi_resp_ready;

  dmi_jtag #(
    .IdcodeValue(IdcodeValue),
    .NumDmiWordAbits(NumDmiByteAbits - 2)
  ) u_dmi_jtag (
    .clk_i,
    .rst_ni,
    .testmode_i       ( scanmode          ),
    .test_rst_ni      ( scan_rst_ni       ),
    .dmi_rst_no       (                   ), // unused
    .dmi_req_o        ( dmi_req           ),
    .dmi_req_valid_o  ( dmi_req_valid     ),
    // unless there is room for response, stall
    .dmi_req_ready_i  ( req_ready         ),
    .dmi_resp_i       ( dmi_resp          ),
    .dmi_resp_ready_o ( dmi_resp_ready    ),
    .dmi_resp_valid_i ( dmi_resp_valid    ),
    .tck_i            ( tck_muxed         ),
    .tms_i            ( jtag_i.tms        ),
    .trst_ni          ( trst_n_muxed      ),
    .td_i             ( jtag_i.tdi        ),
    .td_o             ( jtag_o.tdo        ),
    .tdo_oe_o         ( jtag_o.tdo_oe     )
  );

  // Outstanding request handling.
  logic pending_req_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin : p_pending
    if (!rst_ni) begin
      pending_req_q <= 1'b0;
    end else begin
      // New request
      if (dmi_req_ready && dmi_req_valid && (!pending_req_q)) begin
        pending_req_q <= 1'b1;
      end else if (dmi_resp_valid) begin
        pending_req_q <= 1'b0;
      end
    end
  end

  // DMI to TL-UL transducing
  logic dmi_error;
  tlul_adapter_host #(
    // Only make one request at a time.
    .MAX_REQS(1),
    .EnableDataIntgGen(1)
  ) u_tap_tlul_host (
    .clk_i,
    .rst_ni,
    // Do not make more than one request at a time
    .req_i        ( dmi_req_valid && !pending_req_q        ),
    .gnt_o        ( dmi_req_ready                          ),
    .addr_i       ( top_pkg::TL_AW'({dmi_req.addr, 2'b00}) ),
    .we_i         ( dmi_req.op == dm::DTM_WRITE            ),
    .wdata_i      ( dmi_req.data                           ),
    .wdata_intg_i ('0                                      ),
    .be_i         ( {top_pkg::TL_DBW{1'b1}}                ),
    .user_rsvd_i  ('0                                      ),
    .instr_type_i ( prim_mubi_pkg::MuBi4False              ),
    .valid_o      ( dmi_resp_valid                         ),
    .rdata_o      ( dmi_resp.data                          ),
    .rdata_intg_o (                                        ),
    .err_o        ( dmi_error                              ),
    .intg_err_o   (                                        ),
    .tl_o         ( tl_h2d_o                               ),
    .tl_i         ( tl_d2h_i                               )
  );

  // We use the user channel to transmit the DMI response type.
  assign dmi_resp.resp = (dmi_error) ? dm::DTM_ERR : dm::DTM_SUCCESS;

  // These signals are unused
  logic unused_tap_tl_d2h;
  assign unused_tap_tl_d2h = ^{
    tl_d2h_i.d_opcode,
    tl_d2h_i.d_param,
    tl_d2h_i.d_size,
    tl_d2h_i.d_source,
    tl_d2h_i.d_sink,
    tl_d2h_i.d_error
  };

endmodule : tlul_jtag_dtm
