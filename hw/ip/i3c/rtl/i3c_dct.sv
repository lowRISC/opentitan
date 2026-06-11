// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Device Characteristics Table (HCI 8.2).
//
// - conveys the properties of each assigned Target to the driver software.
// - hardware requires only write access and has highest priority.
module i3c_dct
  import i3c_pkg::*;
  import prim_ram_1p_pkg::*;
#(
  parameter int unsigned DataWidth = 32,
  parameter int unsigned NumDCTEntries = i3c_pkg::NumDCTEntries,

  localparam int unsigned DCTMemWidth = $bits(i3c_dct_mem_t),
  // Derived parameters.
  localparam int unsigned DCTMaskW = (DCTMemWidth + 7) / 8,
  localparam int unsigned DCTAddrW = $clog2(NumDCTEntries)
) (
  input                   clk_i,
  input                   rst_ni,

  // Hardware interface.
  input                   dct_we_i,
  input    [DCTAddrW-1:0] dct_idx_i,
  input    [DCTMaskW-1:0] dct_wmask_i,
  input     i3c_dct_mem_t dct_wdata_i,

  // HCI Device Characteristics Table interface.
  input                   sw_dct_req_i,
  output                  sw_dct_gnt_o,
  input                   sw_dct_we_i,
  input    [DCTAddrW+1:0] sw_dct_addr_i,
  input   [DataWidth-1:0] sw_dct_wdata_i,
  output                  sw_dct_rvalid_o,
  output  [DataWidth-1:0] sw_dct_rdata_o,

  // DFT-related signals.
  input  ram_1p_cfg_t     dct_cfg_i,
  output ram_1p_cfg_rsp_t dct_cfg_rsp_o
);

  // The CPU cannot access the full DCT Entry in a single access; its bus is narrower.
  localparam int unsigned DCTEntryWidth = $bits(i3c_dct_entry_t);
  localparam int unsigned DCTWidthWords = (DCTEntryWidth + DataWidth - 1) / DataWidth;
  localparam int unsigned Log2DW = $clog2(DataWidth);

  logic [DCTMaskW-1:0] sw_dct_wmask;
  i3c_dct_mem_t sw_dct_wdata_packed;
  i3c_dct_entry_t sw_dct_wdata_full;
  assign sw_dct_wdata_full = i3c_dct_entry_t'({DCTWidthWords{sw_dct_wdata_i}});

  always_comb begin
    sw_dct_wmask = '0;
    // The DCT entry is mapped into a number of CPU memory locations, but with
    // holes (HCI Table 131).
    case (sw_dct_addr_i[1:0])
      2'b00: sw_dct_wmask[3:0] = 4'hF;
      2'b01: sw_dct_wmask[5:4] = 2'b11;
      2'b10: sw_dct_wmask[7:6] = 2'b11;
      default: sw_dct_wmask[8] = 1'b1;
    endcase

    sw_dct_wdata_packed.dynamic_address = sw_dct_wdata_full.dynamic_address;
    sw_dct_wdata_packed.bcr = sw_dct_wdata_full.bcr;
    sw_dct_wdata_packed.dcr = sw_dct_wdata_full.dcr;
    sw_dct_wdata_packed.pid_lo = sw_dct_wdata_full.pid_lo;
    sw_dct_wdata_packed.pid_hi = sw_dct_wdata_full.pid_hi;
  end

  i3c_dct_entry_t sw_dct_rdata_full;
  i3c_dct_mem_t sw_dct_rdata_packed;
  logic [DCTMemWidth-1:0] sw_dct_rdata_raw;
  assign sw_dct_rdata_packed = i3c_dct_mem_t'(sw_dct_rdata_raw);

  always_comb begin
    sw_dct_rdata_full = '0;  // Zero-initialize the reserved fields.
    sw_dct_rdata_full.dynamic_address = sw_dct_rdata_packed.dynamic_address;
    sw_dct_rdata_full.bcr             = sw_dct_rdata_packed.bcr;
    sw_dct_rdata_full.dcr             = sw_dct_rdata_packed.dcr;
    sw_dct_rdata_full.pid_lo          = sw_dct_rdata_packed.pid_lo;
    sw_dct_rdata_full.pid_hi          = sw_dct_rdata_packed.pid_hi;
  end

  // Extract the appropriate CPU word from the DCT entry to return it.
  logic [1:0] sw_dct_rdata_sel;
  assign sw_dct_rdata_o = DataWidth'(sw_dct_rdata_full >> {sw_dct_rdata_sel, Log2DW'(0)});

  // Device Characteristics Table.
  i3c_dxt #(
    .EntryWidth (DCTMemWidth),
    .NumEntries (NumDCTEntries),
    .MaskWidth  (DCTMaskW),
    .OOBWidth   (2)
  ) u_dct(
    .clk_i      (clk_i),
    .rst_ni     (rst_ni),

    // Port A (hardware; highest priority).
    .a_re_i     (1'b0),
    .a_we_i     (dct_we_i),
    .a_idx_i    (dct_idx_i),
    .a_wmask_i  (dct_wmask_i),
    .a_wdata_i  (dct_wdata_i),
    .a_rdata_o  (),

    // Port B (software; lowest priority).
    .b_req_i    (sw_dct_req_i),
    .b_gnt_o    (sw_dct_gnt_o),
    .b_we_i     (sw_dct_we_i),
    .b_idx_i    (sw_dct_addr_i[DCTAddrW+1:2]),
    .b_wmask_i  (sw_dct_wmask),
    .b_wdata_i  (sw_dct_wdata_packed),
    .b_oob_i    (sw_dct_addr_i[1:0]),
    .b_rvalid_o (sw_dct_rvalid_o),
    .b_rdata_o  (sw_dct_rdata_raw),
    .b_oob_o    (sw_dct_rdata_sel),

    .cfg_i      (dct_cfg_i),
    .cfg_rsp_o  (dct_cfg_rsp_o)
  );

endmodule
