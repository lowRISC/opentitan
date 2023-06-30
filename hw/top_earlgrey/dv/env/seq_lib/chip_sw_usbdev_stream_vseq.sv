// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_usbdev_stream_vseq extends chip_sw_usbdev_dpi_vseq;
  `uvm_object_utils(chip_sw_usbdev_stream_vseq)

  `uvm_object_new

  virtual task cpu_init();
    // sw_symbol_backdoor_overwrite takes an array as the input
    bit [7:0] stream_count[1];
    bit [7:0] stream_retrying[1];
    bit [7:0] stream_max_packets[1];
    super.cpu_init();

    // Number of streams to exercise concurrently; by default exercise all available
    // endpoints/streams.
    if (!$value$plusargs("sw_usbdev_stream_count=%0d", stream_count[0])) begin
      stream_count[0] = 8'h0B;
    end

    // Retrying exercises the ACK/NAK logic within usbdev, and should normally
    // be enabled.
    if (!$value$plusargs("sw_usbdev_stream_retrying=%0d", stream_retrying[0])) begin
      stream_retrying[0] = 8'h01;
    end

    // Maximum-length packets are required for testing transmission/reception at
    // frequency extremes. It should normally be disabled, to randomize packet
    // sizes.
    if (!$value$plusargs("sw_usbdev_stream_max_packets=%0d", stream_max_packets[0])) begin
      stream_max_packets[0] = 8'h00;
    end

    // Present the configuration to the usbdev_stream_test software
    sw_symbol_backdoor_overwrite("kNumStreams", stream_count);
    sw_symbol_backdoor_overwrite("kRetrying", stream_retrying);
    sw_symbol_backdoor_overwrite("kMaxPackets", stream_max_packets);
  endtask

  // TODO: introduce randomization to make this test more useful; candidates:
  // - number of endpoints
  // - response timing of DPI model
  // - stream test flags (transfer direction(s) ...)

  virtual task body();
    super.body();
  endtask

endclass : chip_sw_usbdev_stream_vseq
