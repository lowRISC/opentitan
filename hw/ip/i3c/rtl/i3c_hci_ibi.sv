// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// In-Band Interrupt (IBI) Status handling; HCI/Driver side, reading from queues.

`include "prim_assert.sv"

module i3c_hci_ibi
  import i3c_pkg::*;
(
  input         clk_i,
  input         rst_ni,

  // Software reset to the FIFO; resets this counting logic too.
  input         sw_reset_i,

  // Indication of whether the next word is a status descriptor.
  output        status_o,

  // Reading from IBI Status Descriptor FIFO and IBI Queue.
  input         read_i,  // Read has occurred, advance internal state.
  input  [31:0] rdata_i  // DWORD just read.
);

  // - HCI-side of the IBI Status handling, reading from the two queues.
  // - Switches between the reading of IBI Status Descriptors and their associated data DWORDs,
  //   by counting DWORDs on the read side.
  // - This is simpler than the write side; see `i3c_controller_ibi` for more detail.

  // Segments can consist of up to 252 bytes, equating to 63 DWORDs/queue entries.
  // - the write side may have further limited the segment length according to the physical depth of
  //   the IBI queue and the configured `DATA_SEGMENT_SIZE`.
  localparam int unsigned SegCntW = 6;

  // Interpret the DWORD as an IBI Status Descriptor; we are concerned only with the descriptors.
  i3c_ibi_status_t stat_desc;
  assign stat_desc = i3c_ibi_status_t'(rdata_i);

  // Data lengths in words; payload lengths are described in bytes, so we must round up here.
  // - `ibi_controller_ibi` shall not emit more than 63 DWORDs (252 bytes) per segment so this
  //   addition cannot overflow.
  wire [7:2] rd_words = stat_desc.data_length[7:2] + |stat_desc.data_length[1:0];

  logic [SegCntW-1:0] rd_words_left;

  // Indicate whether this read word is an IBI Status Descriptor.
  assign status_o = ~|rd_words_left;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) rd_words_left <= '0;
    else if (sw_reset_i) rd_words_left <= '0;
    else if (read_i) begin
      // Read side just requires down-counting until the next status descriptor.
      rd_words_left <= status_o ? rd_words : (rd_words_left - 'b1);
    end
  end

  // Check that `i3c_controller_ibi` does not attempt to describe a segment of more than 252 bytes.
  `ASSERT(DataLengthValidA, stat_desc.data_length <= 8'hfc || !read_i || !status_o)

endmodule
