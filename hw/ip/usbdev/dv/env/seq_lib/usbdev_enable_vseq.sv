// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_enable_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_enable_vseq)

  `uvm_object_new

  task pre_start();
    // need to disable device init.
    // This sequence is designed to assess the functionality of the USB_CTRL register's
    // enable field. During device initialization, the device is automatically enabled.
    // Therefore, if we want to accurately test the device enable function,
    // we need to manually set this.
    do_usbdev_init = 1'b0;

    super.pre_start();
  endtask

  task body();
    uvm_reg_data_t rd_data;

    usbdev_connect();
    wait_for_link_state({LinkActive, LinkActiveNoSOF}, 10 * 1000 * 48);  // 10ms timeout, at 48MHz
    usbdev_set_address(dev_addr);

    configure_out_trans(); // register configurations for OUT Trans.

    // Enable pkt_received interrupt
    ral.intr_enable.pkt_received.set(1'b1);
    csr_update(ral.intr_enable);

    call_token_seq(PidTypeOutToken);
    cfg.clk_rst_vif.wait_clks(10);
    call_data_seq(PidTypeData0, .randomize_length(1'b0), .num_of_bytes(8));
    get_response(m_response_item);
    $cast(m_usb20_item, m_response_item);
    m_usb20_item.check_pid_type(PidTypeAck);

    // Check that the USB device received a packet with the expected properties.
    check_pkt_received(endp, 0, out_buffer_id, m_data_pkt.data);
  endtask

endclass
