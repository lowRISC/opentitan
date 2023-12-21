// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usb20_driver extends dv_base_driver #(usb20_item, usb20_agent_cfg);
  `uvm_component_utils(usb20_driver)

  `uvm_component_new

  int usb_rst_time = 100_000;  // upto 10ms
  int usb_idle_clk_cycles = 5;
  bit [7:0] SYNC_PATTERN = 8'b1000_0000;
  bit [1:0] EOP = 2'b00;
  token_pkt m_token_pkt;
  data_pkt  m_data_pkt ;
  handshake_pkt m_handshake_pkt;

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(virtual usb20_block_if)::get(this, "*.env.m_usb20_agent*",
                                                     "bif", cfg.bif)) begin
      `uvm_fatal(`gfn, "Failed to get usb20_block_if handle from uvm_config_db")
    end
  endfunction

  virtual task run_phase(uvm_phase phase);
    forever begin
      reset_signals();
      get_and_drive();
    end
  endtask

  // get_and_drive Task
  // -------------------------------
  virtual task get_and_drive();
    usb20_item seq_item;
    usb20_item rsp_item;
    forever begin
      if (cfg.if_mode == Host) begin
        seq_item_port.get_next_item(seq_item);
        $cast(rsp_item, seq_item.clone());
        rsp_item.set_id_info(seq_item);
        if (seq_item.m_pkt_type == PktTypeToken) begin
          prepare_token_packet(seq_item, rsp_item);
        end else if (seq_item.m_pkt_type == PktTypeData) begin
          prepare_data_packet(seq_item, rsp_item);
        end else if (seq_item.m_pkt_type == PktTypeHandshake) begin
          prepare_handshake_packet(seq_item, rsp_item);
        end else if (seq_item.m_pkt_type == PktTypeSoF) begin
          prepare_sof_packet(seq_item, rsp_item);
        end
      end
    end
  endtask

  task prepare_token_packet(usb20_item seq_item, usb20_item rsp_item);
    bit driver_token_pkt[];
    bit comp_token_pkt[];
    $cast(m_token_pkt, seq_item);
    m_token_pkt.print();
    // Modified each field of the packet to start with the Least Significant Bit (LSB)
    m_token_pkt.m_pid_type = {<<4{m_token_pkt.m_pid_type}};
    m_token_pkt.m_pid_type = {<<{m_token_pkt.m_pid_type}};
    m_token_pkt.address = {<<{m_token_pkt.address}};
    m_token_pkt.endpoint = {<<{m_token_pkt.endpoint}};
    m_token_pkt.crc5 = {<<{m_token_pkt.crc5}};
    m_token_pkt.pack(driver_token_pkt);
    // to make complete packet need to attach SYNC at start of packet
    comp_token_pkt = new[driver_token_pkt.size() + 8];
    for (int i = 0; i < 8; i++) begin
      comp_token_pkt[i] = SYNC_PATTERN[i];
    end
    for (int i = 0; i < driver_token_pkt.size(); i++) begin
      comp_token_pkt[i + 8] = driver_token_pkt[i];
    end
    `uvm_info(`gfn, $sformatf("Complete Token_Packet = %p", comp_token_pkt), UVM_DEBUG)
    drive_pkt(comp_token_pkt);
    if (seq_item.m_pid_type == PidTypeInToken) begin
      get_dut_response(rsp_item);
      seq_item_port.item_done(rsp_item);
      `uvm_info (`gfn, $sformatf("In drive afer In packet : \n %0s", rsp_item.sprint()), UVM_DEBUG)
    end else begin
      seq_item_port.item_done();
    end
  endtask

  task prepare_data_packet (usb20_item seq_item, usb20_item rsp_item);
    bit driver_data_pkt[];
    bit comp_data_pkt[];
    $cast(m_data_pkt, seq_item);
    m_data_pkt.print();
    // Modified each field of the packet to start with the Least Significant Bit (LSB)
    m_data_pkt.m_pid_type = {<<4{m_data_pkt.m_pid_type}};
    m_data_pkt.m_pid_type = {<<{m_data_pkt.m_pid_type}};
    m_data_pkt.data = {<<8{m_data_pkt.data}};
    m_data_pkt.data = {<<{m_data_pkt.data}};
    m_data_pkt.crc16 = {<<{m_data_pkt.crc16}};
    m_data_pkt.pack(driver_data_pkt);
    `uvm_info(`gfn, $sformatf("Driver Data_Packet = %p", driver_data_pkt), UVM_DEBUG)
    // To make complete packet need to attach SYNC at start of packet
    comp_data_pkt = new[driver_data_pkt.size() + 8];
    for (int i = 0; i < 8; i++) begin
      comp_data_pkt[i] = SYNC_PATTERN[i];
    end
    for (int i = 0; i < driver_data_pkt.size(); i++) begin
      comp_data_pkt[i + 8] = driver_data_pkt[i];
    end
    `uvm_info(`gfn, $sformatf("Complete Data_Packet = %p", comp_data_pkt), UVM_DEBUG)
    drive_pkt(comp_data_pkt);
    get_dut_response(rsp_item);
    seq_item_port.item_done(rsp_item);
  endtask

  task prepare_handshake_packet(usb20_item seq_item, usb20_item rsp_item);
    bit driver_handshake_pkt[];
    bit comp_handshake_pkt[];
    $cast(m_handshake_pkt, seq_item);
    m_handshake_pkt.m_pid_type = {<<4{m_handshake_pkt.m_pid_type}};
    m_handshake_pkt.m_pid_type = {<<{m_handshake_pkt.m_pid_type}};
    m_handshake_pkt.pack(driver_handshake_pkt);
    `uvm_info(`gfn, $sformatf("Driver Handshake_Packet = %p", driver_handshake_pkt), UVM_DEBUG)
    // To make complete packet need to attach SYNC at start of packet
    comp_handshake_pkt = new[driver_handshake_pkt.size() + 8];
    for (int i = 0; i < 8; i++) begin
      comp_handshake_pkt[i] = SYNC_PATTERN[i];
    end
    for (int i = 0; i < driver_handshake_pkt.size(); i++) begin
      comp_handshake_pkt[i + 8] = driver_handshake_pkt[i];
    end
    `uvm_info(`gfn, $sformatf("Complete Handshake_Packet = %p", comp_handshake_pkt), UVM_DEBUG)
    drive_pkt(comp_handshake_pkt);
    seq_item_port.item_done();
  endtask

  task  prepare_sof_packet( usb20_item seq_item, usb20_item rsp_item);
    // TODO: Drive method to drive SOF packet
  endtask

  task drive_pkt(bit comp_pkt[]);
    bit nrzi_out[];
    bit bit_stuff_out[];
    // Bit Stuffing performed on packet
    bit_stuffing(comp_pkt, bit_stuff_out);
    `uvm_info(`gfn, $sformatf("Complete Packet after BIT STUFFING = %p", bit_stuff_out), UVM_DEBUG)
    // NRZI Implementation
    nrzi_encoder(bit_stuff_out, nrzi_out);
    `uvm_info(`gfn, $sformatf("Complete Packet after NRZI = %p", nrzi_out), UVM_DEBUG)
    // Loop to drive packet bit by bit
    for (int i = 0; i < nrzi_out.size(); i++) begin
      @(posedge cfg.bif.usb_clk) begin
        cfg.bif.drive_p =  nrzi_out[i];
        cfg.bif.drive_n = ~nrzi_out[i];
      end
    end
    end_of_packet();
  endtask

  // EOP Task
  // -------------------------------
  task end_of_packet();
    for (int j = 0; j < 2; j++) begin
      @(posedge cfg.bif.usb_clk)
      cfg.bif.drive_p =  EOP[j];
      cfg.bif.drive_n =  EOP[j];
    end
    @(posedge cfg.bif.usb_clk) begin
      `uvm_info(`gfn, "\n After EOP Idle state", UVM_DEBUG)
      cfg.bif.drive_p = 1'b1;
      cfg.bif.drive_n = 1'b0;
    end
  endtask

  // Bit Stuffing Task
  // -------------------------------
  task bit_stuffing(input bit packet[], output bit bit_stuff_out[]);
    int consecutive_ones_count = 0;
    for (int i = 0; i < packet.size(); i++) begin
      if (packet[i] == 1'b1) begin
        consecutive_ones_count = consecutive_ones_count + 1;
        if (consecutive_ones_count == 6) begin
          packet = new[packet.size() + 1](packet);
          for (int j = packet.size() ; j > i; j = j - 1) begin
            packet[j] = packet[j - 1];
          end
          i = i + 1;
          packet[i] = 1'b0;
          consecutive_ones_count = 0;
        end
      end else if (packet[i] == 1'b0) begin
        consecutive_ones_count = 0;
      end
    end
    bit_stuff_out = packet;
  endtask

  // NRZI Encoding/Decoding Task
  // -------------------------------

  task nrzi_encoder(input bit packet[], output bit nrzi_out[]);
    bit prev_bit = 1'b1;
    nrzi_out = new[packet.size()];
    for (int i = 0; i < packet.size(); i++) begin
      if (packet[i] == 1'b0) begin
        nrzi_out[i] = ~prev_bit;
      end else begin
        nrzi_out[i] = prev_bit;
      end
      prev_bit = nrzi_out[i];
    end
  endtask

  task nrzi_decoder(input bit nrzi_in[], output bit decoded_packet[]);
    bit prev_bit = 1'b1;
    decoded_packet = new[nrzi_in.size()];
    for (int i = 0; i < nrzi_in.size(); i++) begin
      if (nrzi_in[i] == prev_bit) begin
        // If the current NRZI bit matches the previous bit, it's a 0.
        decoded_packet[i] = 1'b1;
      end else begin
        // If the current NRZI bit is different from the previous bit, it's a 1.
        decoded_packet[i] = 1'b0;
      end
      prev_bit = nrzi_in[i];
    end
  endtask

  // RESET signals  Task
  // -------------------------------
  virtual task reset_signals();
    cfg.bif.usb_rx_d_i = 1'b1;
    cfg.bif.usb_vbus = 1'b1;
    cfg.bif.drive_p  = 1'b1;
    cfg.bif.drive_n = 1'b1;
    @(posedge cfg.bif.rst_ni);
    `uvm_info(`gfn, "Hardware Reset in Progress", UVM_DEBUG)
    cfg.bif.usb_vbus = 1'b0;
    cfg.bif.drive_p   = 1'bz;
    cfg.bif.drive_n   = 1'bz;
    repeat(usb_idle_clk_cycles) @(posedge cfg.bif.usb_clk);
    cfg.bif.usb_vbus = 1'b1;
    cfg.bif.drive_p   = 1'b1;
    cfg.bif.drive_n   = 1'b0;
    `uvm_info(`gfn, "Out of Hardware Reset", UVM_DEBUG)
    bus_reset();
  endtask

  // USB Bus Reset Task
  // -------------------------------
  task bus_reset();
    @(posedge cfg.bif.usb_clk)
    cfg.bif.drive_p = 1'b1;
    cfg.bif.drive_n = 1'b0;
    // Waitfor device active state
    `DV_SPINWAIT(wait(cfg.bif.usb_dp_pullup_o);, "timeout waiting for usb_pullup", 500_000)
    @(posedge cfg.bif.usb_clk)
    cfg.bif.drive_p = 1'b0;
    cfg.bif.drive_n = 1'b0;
    // Reset bus or drive 0 on both DP and DN for 10ms
    repeat(usb_rst_time) @(posedge cfg.bif.usb_clk);
    `uvm_info(`gfn, "Reset for 10ms completed", UVM_DEBUG)
    // After reset change state to IDLE
    @(posedge cfg.bif.usb_clk)
    cfg.bif.drive_p = 1'b1;
    cfg.bif.drive_n = 1'b0;
    repeat(usb_idle_clk_cycles) @(posedge cfg.bif.usb_clk);
  endtask

  // Get_DUT_Response
  // -------------------------------
  task get_dut_response(usb20_item rsp_item);
    bit received_pkt[];
    bit decoded_received_pkt[];
    int receive_index = 0;
    bit [7:0] received_pid = 0;
    `uvm_info(`gfn, "After drive Packet in wait to check usb_dp_en_o signal", UVM_DEBUG)
    wait(cfg.bif.usb_dp_en_o);
    while (cfg.bif.usb_dp_en_o) begin
      received_pkt = new[received_pkt.size() + 1](received_pkt);
      @(posedge cfg.bif.usb_clk)
      received_pkt[receive_index] = cfg.bif.usb_p;
      receive_index = receive_index + 1;
    end
    `uvm_info(`gfn, $sformatf("Received Packet = %p", received_pkt), UVM_LOW)
    nrzi_decoder (received_pkt, decoded_received_pkt);
    `uvm_info(`gfn, $sformatf("Decoded Received Packet = %p", decoded_received_pkt), UVM_LOW)
    for (int i = 0 ; i < 8; i++) begin
      received_pid[i] = decoded_received_pkt[i + 8];
    end
    received_pid = {<<4{received_pid}};
    rsp_item.m_pid_type = received_pid;
  endtask
endclass
