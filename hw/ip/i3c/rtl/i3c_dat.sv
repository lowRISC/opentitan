// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Device Address Table (HCI 8.1).
//
// - conveys information about each currently-addressable Target from the driver software to the
//   hardware.
// - hardware requires only read access and has highest priority.
module i3c_dat
  import i3c_pkg::*;
  import prim_ram_1p_pkg::*;
#(
  parameter int unsigned DataWidth = 32,
  parameter int unsigned NumDATEntries = i3c_pkg::NumDATEntries,

  localparam int unsigned DATMemWidth = $bits(i3c_dat_mem_t),
  // Derived parameters.
  localparam int unsigned DATAddrW = $clog2(NumDATEntries)
) (
  input                   clk_i,
  input                   rst_ni,

  // Hardware interface.
  input                   dat_re_i,
  input    [DATAddrW-1:0] dat_idx_i,
  output    i3c_dat_mem_t dat_rdata_o,

  // HCI Device Address Table interface.
  input                   sw_dat_req_i,
  output                  sw_dat_gnt_o,
  input                   sw_dat_we_i,
  input      [DATAddrW:0] sw_dat_addr_i,
  input   [DataWidth-1:0] sw_dat_wdata_i,
  output                  sw_dat_rvalid_o,
  output  [DataWidth-1:0] sw_dat_rdata_o,

  // DFT-related signals.
  input  ram_1p_cfg_t     dat_cfg_i,
  output ram_1p_cfg_rsp_t dat_cfg_rsp_o
);

  // The CPU cannot access the full DAT Entry in a single access; its bus is narrower.
  localparam int unsigned DATWidthWords = (DATMemWidth + DataWidth - 1) / DataWidth;

  // We need to track which of the table entries has a dynamic address supplied by the driver
  // software; the memory will start up with undefined contents and nothing in the HCI registers
  // indicates which entries have been populated.
  logic [NumDATEntries-1:0] addr_written;
  logic rdata_valid_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      addr_written  <= '0;
      rdata_valid_q <= 1'b0;
    end else begin
      // Since `rdata_valid_q` modifies the returned dynamic address, keep it stable after reading.
      if (dat_re_i) rdata_valid_q <= addr_written[dat_idx_i];
      if (&{sw_dat_req_i, sw_dat_gnt_o, sw_dat_we_i, !sw_dat_addr_i[0]}) begin
        // Extract the DAT index from the address; each DAT entry occupies two words.
        addr_written[sw_dat_addr_i >> 1] <= 1'b1;
      end
    end
  end

  // Remap the read/write data from/to the packed memory entries.
  i3c_dat_mem_t sw_dat_wmask;
  i3c_dat_mem_t sw_dat_wdata_packed;
  i3c_dat_entry_t sw_dat_wdata_full;
  assign sw_dat_wdata_full = i3c_dat_entry_t'({DATWidthWords{sw_dat_wdata_i}});

  always_comb begin
    // Write strobes for software access to the DAT
    // - individual bit strobes because each DAT entry is presentd to the HCI as as 2 x 32-bit
    //   words, containing 25 and 27 valid data bits; there are no common factors.
    sw_dat_wmask = '0;
    if (sw_dat_addr_i[0]) begin
      sw_dat_wmask.autocmd_hdr_code   = '1;
      sw_dat_wmask.autocmd_mode       = '1;
      sw_dat_wmask.autocmd_value      = '1;
      sw_dat_wmask.autocmd_mask       = '1;
    end else begin
      sw_dat_wmask.device             = '1;
      sw_dat_wmask.dev_nack_retry_cnt = '1;
      sw_dat_wmask.ring_id            = '1;
      sw_dat_wmask.dynamic_address    = '1;
      sw_dat_wmask.ts                 = '1;
      sw_dat_wmask.crr_reject         = '1;
      sw_dat_wmask.ibi_reject         = '1;
      sw_dat_wmask.ibi_payload        = '1;
      sw_dat_wmask.static_address     = '1;
    end

    sw_dat_wdata_packed.autocmd_hdr_code   = sw_dat_wdata_full.autocmd_hdr_code;
    sw_dat_wdata_packed.autocmd_mode       = sw_dat_wdata_full.autocmd_mode;
    sw_dat_wdata_packed.autocmd_value      = sw_dat_wdata_full.autocmd_value;
    sw_dat_wdata_packed.autocmd_mask       = sw_dat_wdata_full.autocmd_mask;
    sw_dat_wdata_packed.device             = sw_dat_wdata_full.device;
    sw_dat_wdata_packed.dev_nack_retry_cnt = sw_dat_wdata_full.dev_nack_retry_cnt;
    sw_dat_wdata_packed.ring_id            = sw_dat_wdata_full.ring_id;
    sw_dat_wdata_packed.dynamic_address    = sw_dat_wdata_full.dynamic_address;
    sw_dat_wdata_packed.ts                 = sw_dat_wdata_full.ts;
    sw_dat_wdata_packed.crr_reject         = sw_dat_wdata_full.crr_reject;
    sw_dat_wdata_packed.ibi_reject         = sw_dat_wdata_full.ibi_reject;
    sw_dat_wdata_packed.ibi_payload        = sw_dat_wdata_full.ibi_payload;
    sw_dat_wdata_packed.static_address     = sw_dat_wdata_full.static_address;
  end

  i3c_dat_entry_t sw_dat_rdata_full;
  i3c_dat_mem_t sw_dat_rdata_packed;
  logic [DATMemWidth-1:0] sw_dat_rdata_raw;
  assign sw_dat_rdata_packed = i3c_dat_mem_t'(sw_dat_rdata_raw);

  always_comb begin
    sw_dat_rdata_full = '0;  // Zero-initialize the reserved fields.
    sw_dat_rdata_full.autocmd_hdr_code   = sw_dat_rdata_packed.autocmd_hdr_code;
    sw_dat_rdata_full.autocmd_mode       = sw_dat_rdata_packed.autocmd_mode;
    sw_dat_rdata_full.autocmd_value      = sw_dat_rdata_packed.autocmd_value;
    sw_dat_rdata_full.autocmd_mask       = sw_dat_rdata_packed.autocmd_mask;
    sw_dat_rdata_full.device             = sw_dat_rdata_packed.device;
    sw_dat_rdata_full.dev_nack_retry_cnt = sw_dat_rdata_packed.dev_nack_retry_cnt;
    sw_dat_rdata_full.ring_id            = sw_dat_rdata_packed.ring_id;
    sw_dat_rdata_full.dynamic_address    = sw_dat_rdata_packed.dynamic_address;
    sw_dat_rdata_full.ts                 = sw_dat_rdata_packed.ts;
    sw_dat_rdata_full.crr_reject         = sw_dat_rdata_packed.crr_reject;
    sw_dat_rdata_full.ibi_reject         = sw_dat_rdata_packed.ibi_reject;
    sw_dat_rdata_full.ibi_payload        = sw_dat_rdata_packed.ibi_payload;
    sw_dat_rdata_full.static_address     = sw_dat_rdata_packed.static_address;
  end

  // Extract the appropriate CPU word from the DCT entry to return it.
  logic sw_dat_rdata_sel;
  assign sw_dat_rdata_o = sw_dat_rdata_sel ? sw_dat_rdata_full[63:32] : sw_dat_rdata_full[31:0];

  i3c_dat_mem_t dat_wdata_packed;
  logic [DATMemWidth-1:0] dat_rdata_raw;
  always_comb begin
    dat_rdata_o = i3c_dat_mem_t'(dat_rdata_raw);
    if (!rdata_valid_q) dat_rdata_o.dynamic_address = '0;
  end

  // Device Address Table.
  i3c_dxt #(
    .EntryWidth (DATMemWidth),
    .NumEntries (NumDATEntries),
    .MaskWidth  (DATMemWidth),
    .OOBWidth   (1)
  ) u_dat(
    .clk_i      (clk_i),
    .rst_ni     (rst_ni),

    // Port A (hardware; highest priority).
    .a_re_i     (dat_re_i),
    .a_we_i     (1'b0),
    .a_idx_i    (dat_idx_i),
    .a_wmask_i  ('0),
    .a_wdata_i  ('0),
    .a_rdata_o  (dat_rdata_raw),

    // Port B (software; lowest priority).
    .b_req_i    (sw_dat_req_i),
    .b_gnt_o    (sw_dat_gnt_o),
    .b_we_i     (sw_dat_we_i),
    .b_idx_i    (sw_dat_addr_i[DATAddrW:1]),
    .b_wmask_i  (sw_dat_wmask),
    .b_wdata_i  (sw_dat_wdata_packed),
    .b_oob_i    (sw_dat_addr_i[0]),
    .b_rvalid_o (sw_dat_rvalid_o),
    .b_rdata_o  (sw_dat_rdata_raw),
    .b_oob_o    (sw_dat_rdata_sel),

    .cfg_i      (dat_cfg_i),
    .cfg_rsp_o  (dat_cfg_rsp_o)
  );

endmodule
