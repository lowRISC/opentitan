// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// SPI Flash Read Command: Read Buffer Manager
/*
The SPI Device IP uses the first half of the DPSRAM as a read buffer. The IP
returns data from the read buffer based on the given address in the received
read command. The read buffer size is 2kB in current design. The IP only uses
lower 11 bits ($clog2(2048)) of the received read command address and uses the
address to issue the read request to the DPSRAM.

It is the SW responsibility to update the read buffer contents. Ths module
provides a SW configurable read watermark CSR and read only
`LAST_READ_ADDRESS` CSR. SW may use those registers to get the time to update
the buffer contents.

The module receives the current sent address and the threshold to determine
the buffer flip and the watermark event. Buffer flip event occurs when the
host system accesses the other side of the buffer. For example, in current
total buffer size 2kB. If the host accesses 0xFFC then 0x1000. The buffer flip
occurs (from Buffer 1 to Buffer 0). In contrast, if the host system crosses
the buffer boundary in opposite direction(0x1000 --> 0xFFC), it is not assumed
as a buffer flip event.

The watermark event happens when the host system accesses the address greater
than the watermark CSR for the first time in a buffer. Let's assume the
threshold (watermark) CSR value is 0x200 (512B). If the host system issues
a SPI read command at the address 0x1FC and read 16B data, the IP keeps
checking the sent address (from 0x1FC then 0x1FD, 0x1FE, 0x1FF) and when it
sends the 0x200 data, it raises a watermark event.

The watermark event is sticky event. It is reported to the SW once and cleared
by the flip event. So even the host system keeps reading 0x1FC and 0x200
multiple times, the event won't be notified to the SW after the first report.
*/

`include "prim_assert.sv"

module spid_readbuffer
  import spi_device_pkg::SramBufferAw, spi_device_pkg::FlashMode;
(
  input clk_i,
  input rst_ni,

  input sys_rst_ni, // to keep the addr, bufidx, flip signals

  input spi_device_pkg::spi_mode_e spi_mode_i,

  input [31:0]             current_address_i,
  input [SramBufferAw-1:0] threshold_i,

  input sfdp_hit_i,
  input mailbox_hit_i,
  input mailbox_en_i,

  // start: data Output phase indicator. Either pulse or level are fine.
  input start_i,

  // The Buffer logic updates its status only at the last beat of the byte.
  // The time is when the address is updated.
  // It is expected that the address is updated at the end of beat of a byte.
  input address_update_i,

  output logic event_watermark_o,
  output logic event_flip_o
);

  ////////////////
  // Definition //
  ////////////////

  typedef enum logic {
    StIdle,
    StActive
  } st_e;
  st_e st_q, st_d;

  ////////////
  // Signal //
  ////////////

  logic watermark_cross;
  logic watermark_crossed; // set by event / clear by flip

  logic flip;

  // The logic keeps next buffer address. Compare this with the
  // current_address and if it hits with mask, then the flip event occurs.
  //
  // ICEBOX(#10038): If the device goes sleep, the next_buffer_addr should be
  //                 recoverable.
  logic [31-SramBufferAw:0] next_buffer_addr;

  logic active;

  //////////////
  // Datapath //
  //////////////

  // Flip event handling
  always_ff @(posedge clk_i or negedge sys_rst_ni) begin
    if (!sys_rst_ni) begin
      next_buffer_addr <= (32-SramBufferAw)'(1); // pointing to next buffer
    end else if (active && flip) begin
      next_buffer_addr <= next_buffer_addr + 1'b 1;
    end
  end

  logic [31-SramBufferAw:0] current_buffer_idx;
  assign current_buffer_idx = current_address_i[31:SramBufferAw];
  assign flip = current_buffer_idx == next_buffer_addr;

  // make flip event single cycle pulse signal
  // It will be synchronized into the bus clock domain using prim_pulse_sync
  logic flip_q;
  always_ff @(posedge clk_i or negedge sys_rst_ni) begin
    if (!sys_rst_ni) flip_q <= 1'b 0;
    else if (active) flip_q <= flip;
  end

  assign event_flip_o = active && flip && !flip_q;

  // ICEBOX(#10037): Consider the case if host jumps the address? (report
  //                 error?)

  // ICEBOX(#10038): Consider the case of sleep and recover. Provide a way to
  //                 recover `next_buffer_addr`?

  // Watermark event: Threshold should not be 0 to enable the event
  assign watermark_cross = (current_address_i[SramBufferAw-1:0] >= threshold_i)
                         && |threshold_i;

  always_ff @(posedge clk_i or negedge sys_rst_ni) begin
    if (!sys_rst_ni) begin
      watermark_crossed <= 1'b 0;
    end else if (active && watermark_cross) begin
      // When `watermark_cross` and `flip` both are 1, the watermark_crossed
      // should remain 1. The event will be reported in this case.
      watermark_crossed <= 1'b 1;
    end else if (active && flip) begin
      watermark_crossed <= 1'b 0;
    end
  end

  always_comb begin : watermark_event_logic
    event_watermark_o = 1'b 0;

    if (active && watermark_cross) begin
      if (!watermark_crossed) begin
        event_watermark_o = 1'b 1;
      end else if (flip) begin
        // if flip is set and previous watermark_crossed is set, the event
        // should be reported also. This means the host issues the next buffer
        // address pointing above the threshold. This scenario, flip event and
        // watermark event both should be reported.
        event_watermark_o = 1'b 1;
      end
    end
  end : watermark_event_logic

  ///////////////////
  // State Machine //
  ///////////////////
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) st_q <= StIdle;
    else if (spi_mode_i != spi_device_pkg::FlashMode) begin
      st_q <= StIdle;
    end else begin
      st_q <= st_d;
    end
  end

  always_comb begin
    st_d = st_q;

    active = 1'b 0;

    unique case (st_q)
      StIdle: begin
        if (start_i && (spi_mode_i == spi_device_pkg::FlashMode)
           && !sfdp_hit_i && !(mailbox_en_i && mailbox_hit_i)) begin
          st_d = StActive;

          active = 1'b 1; // Assume address_update_i is high
        end
      end

      StActive: begin
        // Deadend waiting CSb de-assertion
        st_d = StActive;

        active = address_update_i;
      end

      default: begin
        st_d = StIdle;
      end
    endcase
  end

  `ASSERT(StartWithAddressUpdate_A, start_i |-> address_update_i)

endmodule : spid_readbuffer
