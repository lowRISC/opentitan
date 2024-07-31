// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_low_speed_traffic_vseq extends usbdev_max_non_iso_usb_traffic_vseq;
  `uvm_object_utils(usbdev_low_speed_traffic_vseq)

  `uvm_object_new

  // Parallel process that injects low speed traffic in the downstream direction; the streaming
  // test should continue unimpacted aside from taking longer to transmit and check all of the data.
  virtual task generate_low_speed_traffic();
    while (!traffic_stop) begin
      // Device address and endpoint number for the low speed communication.
      bit [6:0] ls_dev_addr;
      bit [3:0] ls_ep;
      // low speed traffic shall be generated with intermediate frequency; it's less intrusive than
      // suspend-resume signaling and bus resets, but it is eight times slower than the equivalent
      // full speed signaling.
      bit [12:0] ls_delay;
      // Decide upon a device address and endpoint for the low speed communications.
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(ls_dev_addr, ls_dev_addr != dev_addr;)
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(ls_ep, ls_ep < NEndpoints;)
      // Decide upon the time interval before the next low speed traffic stimulus.
      `DV_CHECK_STD_RANDOMIZE_FATAL(ls_delay)
      fork
        begin : isolation_fork
          fork
            cfg.clk_rst_vif.wait_clks(ls_delay);
            wait (traffic_stop);
          join_any
          disable fork;
        end : isolation_fork
      join
      claim_driver();
      // Try all packet types; IN, OUT and SETUP transactions, as well as handshake packets.
      // - only the downstream traffic is visible to full speed devices, so the DUT must be able
      //   to ignore OUT, SETUP and handshake packets, as well as IN token packets but it should
      //   never encounter IN DATA packets.
      low_speed_traffic = 1'b1;
      randcase
        1: begin
          // Note: Low Speed DATA packets cannot be more than 8 bytes in length.
          int unsigned num_of_bytes = $urandom_range(0, 8);
          `uvm_info(`gfn, "Generating low speed OUT transaction", UVM_MEDIUM)
          send_prnd_out_packet(ls_ep, ($urandom & 1) ? PidTypeData1 : PidTypeData0,
                               .randomize_length(0), .num_of_bytes(num_of_bytes),
                               .isochronous_transfer(0), .target_addr(ls_dev_addr));
        end
        1: begin
          `uvm_info(`gfn, "Generating low speed IN transaction", UVM_MEDIUM)
          send_token_packet(ls_ep, PidTypeInToken, ls_dev_addr);
        end
        1: begin
          `uvm_info(`gfn, "Generating low speed SETUP transaction", UVM_MEDIUM)
          send_prnd_setup_packet(ls_ep, ls_dev_addr);
        end
        1: begin
          `uvm_info(`gfn, "Generating low speed handshake packet", UVM_MEDIUM)
          send_handshake(($urandom & 1) ? PidTypeNak : PidTypeAck);
        end
      endcase
      low_speed_traffic = 1'b0;
      release_driver();
    end
  endtask

  virtual task body();
    fork
      super.body();
      generate_low_speed_traffic();
    join
  endtask
endclass : usbdev_low_speed_traffic_vseq
