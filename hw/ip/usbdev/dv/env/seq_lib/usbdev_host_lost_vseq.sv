// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_host_lost_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_host_lost_vseq)

  `uvm_object_new

  // Check that the DUT asserts the 'host lost' interrupt after ~4.1ms without receipt of a
  // Start Of Frame (SOF) packet, despite the link being active (non-Idle).
  virtual task body();
    bit host_lost;
    send_sof_packet(PidTypeSofToken);
    // Ensure the interrupt is not already asserted.
    csr_wr(.ptr(ral.intr_state), .value(1 << IntrHostLost));
    // Check that the `host_lost` bit in the `usbstat` register is not yet set.
    csr_rd(.ptr(ral.usbstat.host_lost), .value(host_lost));
    `DV_CHECK_NE(host_lost, 1'b1, "host_lost status bit already asserted")
    // Enable the host lost interrupt.
    csr_wr(.ptr(ral.intr_enable), .value(1 << IntrHostLost));
    fork
      begin : isolation_fork
        fork
          // We must keep sending some traffic in order to keep the link in the active state and
          // prevent the DUT from Suspending.
          forever begin
            send_prnd_out_packet(ep_default, PidTypeData0, .randomize_length(1), .num_of_bytes(0));
            check_no_response();
          end
          // 4.1ms is long enough for host lost to be declared since no Start Of Frame (SOF) packets
          wait_for_interrupt(1 << IntrHostLost, .timeout_clks(4_100 * 48), .clear(0), .enforce(1));
        join_any
        disable fork;
      end : isolation_fork
    join
    // Check that the interrupt line is asserted.
    `DV_CHECK_EQ(cfg.intr_vif.pins[IntrHostLost], 1'b1, "Interrupt signal not asserted")
    // Check the `host_lost` bit in the `usbstat` register too.
    csr_rd(.ptr(ral.usbstat.host_lost), .value(host_lost));
    `DV_CHECK_EQ(host_lost, 1'b1, "host_lost status bit not asserted")
    // Disable the interrupt before completing.
    csr_wr(.ptr(ral.intr_enable), .value(0));
    clear_all_interrupts();
  endtask

endclass : usbdev_host_lost_vseq
