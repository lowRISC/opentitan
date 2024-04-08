// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_pending_in_trans_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_pending_in_trans_vseq)

  `uvm_object_new

  task body();
    uvm_reg_data_t config_in;
    // register configurations for Setup Trans.
    configure_setup_trans();
    // register configurations for IN Trans.
    configure_in_trans(in_buffer_id, 0);
    csr_rd(ral.configin[endp], config_in);
    `DV_CHECK_EQ(get_field_val(ral.configin[endp].rdy, config_in), 1);
    `DV_CHECK_EQ(get_field_val(ral.configin[endp].pend, config_in), 0);
    // Following the IN configuration, send a packet with a setup token
    // to cancel any pending IN transactions. The device will prioritize
    // the setup transaction by clearing the 'rdy' bit in the configin register.
    call_token_seq(PidTypeSetupToken);
    inter_packet_delay();
    call_data_seq(PidTypeData0, .randomize_length(1'b1), .num_of_bytes(0));
    get_response(m_response_item);
    $cast(m_usb20_item, m_response_item);
    m_usb20_item.check_pid_type(PidTypeAck);
    // Verify that after the setup transaction, the waiting IN transction is canceled
    // by checking 'rdy' and 'pend' bit of configin register.
    csr_rd(ral.configin[endp], config_in);
    `DV_CHECK_EQ(get_field_val(ral.configin[endp].rdy, config_in), 0);
    `DV_CHECK_EQ(get_field_val(ral.configin[endp].pend, config_in), 1);
  endtask
endclass
