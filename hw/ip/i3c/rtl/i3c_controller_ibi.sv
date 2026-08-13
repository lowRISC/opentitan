// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// In-Band Interrupt (IBI) Status handling; Controller side, writing into queues.

module i3c_controller_ibi
  import i3c_pkg::*;
(
  input                   clk_i,
  input                   rst_ni,

  // Controller enable.
  input                   enable_i,

  // Software reset to the FIFO; resets this counting logic too.
  input                   sw_reset_i,

  // Configuration.
  input             [7:0] ibi_status_size_i,  // Size of IBI Status Descriptors and Data Queue.
  input             [7:0] data_seg_size_i,    // Maximum size of IBI Data Segments (1-63 DWORDs).

  // Indication of whether the _next_ DWORD terminates the current segment.
  output                  last_o,

  // Writes into the IBI Status Descriptor FIFO and IBI Data Queue.
  input                   init_i,        // Initialize counting at the start of collecting IBI data.
  input                   write_i,       // Write has occurred, advance internal state.
  input  i3c_ibi_status_t wstat_desc_i,  // Proposed IBI Status Descriptor.

  // Modified IBI Status Descriptor to be written into the FIFO; `DATA_LENGTH` has been updated
  // with the DWORD count, but not byte-level granularity for the final DWORD.
  output i3c_ibi_status_t stat_desc_o
);
  // Note that this handles more than In-Band Interrupts, since as of HCI version 1.2 a number of
  // other event/status indications are also passed through the IBI Queue.
  //
  // - Each IBI/event is decomposed into `segments`, each segment being described by an IBI Status
  //   Descriptor (`i3c_ibi_status_t`).
  // - This module maintains the necessary metadata alongside the IBI Queue itself and decomposes
  //   longer IBIs into segments so that they may be streamed through a shorter queue.
  // - The IBI Data Queue holds only the data words because the data must be stored before its
  //   associated IBI Status Descriptor can be completed.
  // - Yes, on the HCI/Driver side, the descriptor must be presented _before_ the data that it
  //   describes.
  // - The IBI Status Descriptors are therefore held in a separate logical FIFO.
  // - The Status words (`i3c_ibi_status_t`) give the lengths of the following data, but it remains
  //   necessary to count the number of payload words still to be written/read at each end of the
  //   FIFO.

  // Segments can consist of up to 252 bytes, equating to 63 DWORDs (FIFO entries).
  localparam int unsigned SegCntW = 6;

  // The IBI Queue Size is specified in units of 8 DWORDs; since the data DWORDs must be written
  // before the IBI Status Descriptor, we cannot describe a segment larger than the IBI Queue Size.
  // The IBI Data Segments are limited to a maximum of 63 DWORDs by `IBI_DATA_SEGMENT_SIZE`
  // (HCI Table 41).
  logic [5:0] ibi_status_size_clamped;
  assign ibi_status_size_clamped = |ibi_status_size_i[7:3] ? 6'h3f : {ibi_status_size_i[2:0], 3'b0};

  // Clamp the DATA_SEGMENT_SIZE value to something sensible; if it exceeded the size of the
  // IBI Data Queue it would be impossible to receive IBIs longer than the queue.
  wire [5:0] seg_dwords = (ibi_status_size_clamped < data_seg_size_i) ? ibi_status_size_clamped
                                                                      : data_seg_size_i[5:0];
  // Counts of payload DWORDs written.
  // - an IBI with a data payload exceeding `IBI_DATA_SEGMENT_SIZE` DWORDs or the IBI Queue Size
  //   must be split into multiple segments.
  logic [SegCntW-1:0] dwords_written;
  logic [SegCntW-1:0] dwords_next;
  assign dwords_next = dwords_written + 'b1;

  // Emit the modified IBI Status Descriptor.
  always_comb begin
    // Copy everything across, except for populating the `data_length` field.
    // - this module tracks only DWORDs, as returned by the transceiver logic.
    // - the parent is responsible for completing bits [1:0] with the byte count of the final DWORD.
    stat_desc_o = wstat_desc_i;
    stat_desc_o.data_length = {dwords_written, 2'b00};
  end

  // Indicate whether the next word terminates the current segment; this instructs the controller
  // core to issue another IBI Status Descriptor.
  assign last_o = (dwords_next >= seg_dwords);

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) dwords_written <= '0;
    else if (sw_reset_i) dwords_written <= '0;
    else if (enable_i & (init_i | write_i)) begin
      // Reset the DWORD count when starting an IBI transfer or completing a segment.
      dwords_written <= (init_i | last_o) ? 'b0 : dwords_next;
    end
  end

endmodule
