// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_phy_config_eop_single_bit_handling_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_phy_config_eop_single_bit_handling_vseq)

  `uvm_object_new

  task body();
    // Set single_bit_SE0 flag then usb20_agent will drive single SE0 as EoP.
    cfg.m_usb20_agent_cfg.single_bit_SE0 = 1'b1;
    configure_out_trans(ep_default);
    // Set eop_single_bit field of phy_config register.
    csr_wr (.ptr(ral.phy_config.eop_single_bit), .value(1'b1));

    send_prnd_out_packet(ep_default, PidTypeData0, .randomize_length(1'b1), .num_of_bytes(0));
    check_response_matches(PidTypeAck);
    check_pkt_received(ep_default, 0, out_buffer_id, m_data_pkt.data);
  endtask
endclass
