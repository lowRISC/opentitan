// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_rx_pid_err_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_rx_pid_err_vseq)

  `uvm_object_new

  task body();
    uvm_reg_data_t intr_state;
    bit [7:0] setup_out_pid, data_pid;
    bit is_setup;

    // Configure endpoint to receive SETUP and OUT traffic.
    configure_setup_trans(ep_default);
    configure_out_trans(ep_default);

    // Enable rx_pid_err interrupt.
    csr_wr(.ptr(ral.intr_enable.rx_pid_err), .value(1'b1));

    // Check that the interrupt status bit and the interrupt line are _not_ yet asserted.
    csr_rd(.ptr(ral.intr_state), .value(intr_state));
    `DV_CHECK_EQ(intr_state[IntrRxPidErr], 1'b0, "Interrupt should be asserted yet")
    `DV_CHECK_EQ(cfg.intr_vif.sample_pin(IntrRxPidErr), 1'b0)

    build_prnd_bad_pids(is_setup, setup_out_pid, data_pid);
    send_token_packet(ep_default, pid_type_e'(setup_out_pid));
    inter_packet_delay();
    send_prnd_data_packet(pid_type_e'(data_pid));
    check_no_response();

    // Wait a little while for the interrupt signal to become asserted.
    for (int i = 0; i < 16; i++) begin
      if (1'b1 === cfg.intr_vif.sample_pin(IntrRxPidErr)) break;
      cfg.clk_rst_vif.wait_clks(1);
    end

    // Check that the interrupt has become asserted to inform firmware that a CRC error was
    // detected on an OUT packet; the correct DUT behavior on the USB is simply to ignore the
    // packet; the host will retry the transmission.
    `DV_CHECK_EQ(cfg.intr_vif.sample_pin(IntrRxPidErr), 1'b1)
  endtask
endclass : usbdev_rx_pid_err_vseq
