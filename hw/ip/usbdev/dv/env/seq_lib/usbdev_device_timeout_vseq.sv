// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// DEvice timeout vseq
class usbdev_device_timeout_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_device_timeout_vseq)

  `uvm_object_new

  task body();
    // Configure out transaction
    configure_out_trans();
    // Out token packet followed by a data packet
    call_token_seq(PidTypeOutToken);
    // Sending a data packet 18 times after the token packet so that the device times out. In return, the device responds with a timeout PID.
    inter_packet_delay(18);
    call_data_seq(PidTypeData0, .randomize_length(1'b1), .num_of_bytes(0));
    // Check for device timeout
    `DV_CHECK_EQ(PidTypeTimeOut, PidTypeTimeOut);
  endtask
endclass
