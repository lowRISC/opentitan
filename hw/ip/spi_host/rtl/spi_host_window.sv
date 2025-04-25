// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Module to manage TX & RX FIFO windows for Serial Peripheral Interface (SPI) host IP.
//

module spi_host_window
#(
  parameter bit                             EnableRacl             = 1'b0,
  parameter bit                             RaclErrorRsp           = 1'b1,
  parameter top_racl_pkg::racl_policy_sel_t RaclPolicySelWinRXDATA = 0,
  parameter top_racl_pkg::racl_policy_sel_t RaclPolicySelWinTXDATA = 0
) (
  input  clk_i,
  input  rst_ni,
  input  tlul_pkg::tl_h2d_t rx_win_i,
  output tlul_pkg::tl_d2h_t rx_win_o,
  input  tlul_pkg::tl_h2d_t tx_win_i,
  output tlul_pkg::tl_d2h_t tx_win_o,
  output logic [31:0]       tx_data_o,
  output logic [3:0]        tx_be_o,
  output logic              tx_valid_o,
  input        [31:0]       rx_data_i,
  output logic              rx_ready_o,
  // RACL interface
  input  top_racl_pkg::racl_policy_vec_t racl_policies_i,
  output top_racl_pkg::racl_error_log_t  racl_error_tx_o,
  output top_racl_pkg::racl_error_log_t  racl_error_rx_o
);

  localparam int AW = spi_host_reg_pkg::BlockAw;
  localparam int DW = 32;
  localparam int ByteMaskW = DW / 8;
  localparam top_racl_pkg::racl_range_t [0:0] RaclPolicySelRangesTXDATA = '{
    '{
      base:  {top_pkg::TL_AW{1'b0}},
      limit: {top_pkg::TL_AW{1'b1}},
      policy_sel: top_racl_pkg::racl_policy_sel_t'(RaclPolicySelWinTXDATA),
      enable: 1'b1
    }
  };

  logic         rx_we;

  // Only support reads from the data RX fifo window
  logic  rx_access_error;
  assign rx_access_error = rx_we;

  tlul_adapter_reg_racl #(
    .RegAw             ( AW                       ),
    .RegDw             ( DW                       ),
    .EnableDataIntgGen ( 0                        ),
    .EnableRacl        ( EnableRacl               ),
    .RaclErrorRsp      ( RaclErrorRsp             ),
    .RaclPolicySelVec  ( RaclPolicySelWinRXDATA   )
  ) u_adapter_rx (
    .clk_i,
    .rst_ni,
    .tl_i             ( rx_win_i                  ),
    .tl_o             ( rx_win_o                  ),
    .en_ifetch_i      ( prim_mubi_pkg::MuBi4False ),
    .intg_error_o     (                           ),
    .racl_policies_i  ( racl_policies_i           ),
    .racl_error_o     ( racl_error_rx_o           ),
    .we_o             ( rx_we                     ),
    .re_o             ( rx_ready_o                ),
    .addr_o           (                           ),
    .wdata_o          (                           ),
    .be_o             (                           ),
    .rdata_i          ( rx_data_i                 ),
    .error_i          ( rx_access_error           ),
    .busy_i           ( '0                        )
  );

  // translate bitmask to byte mask
  logic [DW-1:0] bit_mask;
  for (genvar i = 0; i < ByteMaskW; i++) begin : gen_byte_mask
     assign tx_be_o[i] = |bit_mask[i*8 +: 8];

    // all the bits of particular byte must be the same
    `ASSERT(BitMaskCheck_A, (|bit_mask[i*8 +: 8] == 1'b0) ||
                            (&bit_mask[i*8 +: 8] == 1'b1))
  end

  // Only support writes to the data TX fifo window
  tlul_adapter_sram_racl #(
    .SramAw(AW),
    .SramDw(DW),
    .Outstanding(1),
    .ByteAccess(1),
    .ErrOnWrite(0),
    .ErrOnRead(1),
    .EnableRacl(EnableRacl),
    .RaclErrorRsp(RaclErrorRsp),
    .RaclPolicySelNumRanges(1)
  ) u_adapter_tx (
    .clk_i,
    .rst_ni,
    .tl_i(tx_win_i),
    .tl_o(tx_win_o),
    .en_ifetch_i(prim_mubi_pkg::MuBi4False),
    .req_o(tx_valid_o),
    .req_type_o(),
    .gnt_i(1'b1),
    .we_o(),
    .addr_o(),
    .wdata_o(tx_data_o),
    .wmask_o(bit_mask),
    .intg_error_o(),
    .user_rsvd_o(),
    .rdata_i('0),
    .rvalid_i('0),
    .rerror_i('0),
    .compound_txn_in_progress_o(),
    .readback_en_i(prim_mubi_pkg::MuBi4False),
    .readback_error_o (),
    .wr_collision_i(1'b0),
    .write_pending_i(1'b0),
    .racl_policies_i  (racl_policies_i),
    .racl_error_o     (racl_error_tx_o),
    .racl_policy_sel_ranges_i(RaclPolicySelRangesTXDATA)
  );

endmodule : spi_host_window
