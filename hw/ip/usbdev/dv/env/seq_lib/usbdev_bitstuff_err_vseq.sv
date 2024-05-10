// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_bitstuff_err_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_bitstuff_err_vseq)

  `uvm_object_new

  task body();
    bit bitstuff_err;
    configure_out_trans();
    inter_packet_delay();
    call_token_seq(PidTypeOutToken);
    inter_packet_delay();
    `DV_CHECK_EQ(cfg.intr_vif.pins[IntrRxBitstuffErr], 0)
    // Enable bitstuff error
    cfg.m_usb20_agent_cfg.usb_bitstuff_error = 1'b1;
    call_data_seq(PidTypeData0, .randomize_length(1'b1), .num_of_bytes(0));
    get_response(m_response_item);
    $cast(m_usb20_item, m_response_item);
    if (~cfg.m_usb20_agent_cfg.time_out)
      m_usb20_item.check_pid_type(PidTypeAck);
    csr_rd(.ptr(ral.intr_state.rx_bitstuff_err), .value(bitstuff_err));
    `DV_CHECK_EQ(1, bitstuff_err);
  endtask
endclass
