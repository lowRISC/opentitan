// Copyright lowRISC contributors.
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
    num_of_bytes = 8;
    rand_or_not = 0;
    ral.usbctrl.enable.set(1'b1);  // Set usbdev control register enable bit.
    ral.usbctrl.device_address.set(0);
    csr_update(ral.usbctrl);
    cfg.clk_rst_vif.wait_clks(100);
    configure_out_trans(); // register configurations for OUT Trans.
    cfg.clk_rst_vif.wait_clks(20);
    call_token_seq(PktTypeToken, PidTypeOutToken, endp);
    cfg.clk_rst_vif.wait_clks(20);
    call_data_seq(PktTypeData, PidTypeData0, rand_or_not, num_of_bytes);
    get_response(m_response_item);
    $cast(m_usb20_item, m_response_item);
    get_out_response_from_device(m_usb20_item, PidTypeAck);
    cfg.clk_rst_vif.wait_clks(20);
    // Verifies that usb device is enabled and received packet and sends ACK.
    check_trans_accuracy();
    ral.avoutbuffer.buffer.set(set_buffer_id + 1); // Set available buffer id
    csr_update(ral.avoutbuffer);
    csr_wr(.ptr(ral.intr_state), .value(32'h0001_ffff)); // Clear interrupts
  endtask

  task check_trans_accuracy();
    uvm_reg_data_t read_rxfifo;
    uvm_reg_data_t intr_state;
    bit            pkt_received;
    csr_rd(.ptr(ral.rxfifo), .value(read_rxfifo));
    csr_rd(.ptr(ral.intr_state), .value(intr_state));
    pkt_received = bit'(get_field_val(ral.intr_state.pkt_received, intr_state));
    // DV_CHECK on pkt_received interrupt
    `DV_CHECK_EQ(pkt_received, 1);
  endtask
endclass
