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
    // Expected data content of packet
    byte unsigned exp_data[];
    uvm_reg_data_t rd_data;

    ral.usbctrl.enable.set(1'b1);  // Set usbdev control register enable bit.
    ral.usbctrl.device_address.set(0);
    csr_update(ral.usbctrl);

    configure_out_trans(); // register configurations for OUT Trans.

    // Enable pkt_received interrupt
    ral.intr_enable.pkt_received.set(1'b1);
    csr_update(ral.intr_enable);

    call_token_seq(PidTypeOutToken);
    cfg.clk_rst_vif.wait_clks(10);
    call_data_seq(PidTypeData0, .randomize_length(1'b0), .num_of_bytes(8));
    get_response(m_response_item);
    $cast(m_usb20_item, m_response_item);
    get_out_response_from_device(m_usb20_item, PidTypeAck);

    recover_orig_data(m_data_pkt.data, exp_data);
    // Check that the USB device received a packet with the expected properties.
    check_pkt_received(endp, 0, out_buffer_id, exp_data);
  endtask

  // TODO: Presently the act of sending a data packet, destructively modifies it!
  // Restore the data packet to its original state. This just bit-reverses each byte
  // within the input array.
  function void recover_orig_data(input byte unsigned in[], output byte unsigned out[]);
    out = {<<8{in}};  // Reverse the order of the bytes
    out = {<<{out}};  // Bit-reverse everything
  endfunction

endclass
