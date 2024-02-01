// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_setup_trans_ignored_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_setup_trans_ignored_vseq)

  `uvm_object_new

  bit pkt_received = 1;

  task body();
    super.dut_init("HARD");
    csr_wr(.ptr(ral.rxenable_setup[0].setup[endp]), .value(1'b0)); // Disable rx_enable setup
    csr_wr(.ptr(ral.ep_out_enable[0].enable[endp]), .value(1'b1)); // Enable OUT EP
    cfg.clk_rst_vif.wait_clks(10);
    ral.intr_enable.pkt_received.set(1'b1); // Enable pkt_received interrupt
    csr_update(ral.intr_enable);
    // Setup token packet
    call_token_seq(PidTypeSetupToken);
    cfg.clk_rst_vif.wait_clks(20);
    csr_rd(.ptr(ral.intr_state.pkt_received), .value(pkt_received));
    // Verify the packet received bit must be zero.
    // That ensures that device ignored the setup transaction.
    `DV_CHECK_EQ(0, pkt_received);
  endtask
endclass
