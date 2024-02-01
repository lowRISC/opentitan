// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usb20_driver extends dv_base_driver #(usb20_item, usb20_agent_cfg);
  `uvm_component_utils(usb20_driver)

  `uvm_component_new

  int usb_rst_time = 100_000;  // upto 10ms
  int usb_idle_clk_cycles = 5;
  bit [7:0] SYNC_PATTERN = 8'b1000_0000;
  bit [1:0] EOP = 2'b00;

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
    usb20_item req_item;
    usb20_item rsp_item;
    forever begin
      if (cfg.if_mode == Host) begin
        seq_item_port.get_next_item(req_item);
        $cast(rsp_item, req_item.clone());
        rsp_item.set_id_info(req_item);
        case (req_item.m_pkt_type)
          PktTypeToken:     prepare_token_packet(req_item, rsp_item);
          PktTypeData:      prepare_data_packet(req_item, rsp_item);
          PktTypeHandshake: prepare_handshake_packet(req_item, rsp_item);
          PktTypeSoF:       prepare_sof_packet(req_item, rsp_item);
          default: `uvm_fatal(`gfn, $sformatf("Pkt type %x not supported", req_item.m_pkt_type))
        endcase
      end
    end
  endtask

  task prepare_token_packet(usb20_item req_item, usb20_item rsp_item);
    bit driver_token_pkt[];
    bit comp_token_pkt[];
    // Protect sender from modifications to the request item.
    token_pkt pkt;
    $cast(pkt, req_item.clone());
    pkt.print();
    // Modify each field of the packet to start with the Least Significant Bit (LSB)
    pkt.m_pid_type = pid_type_e'({<<{pkt.m_pid_type}});
    pkt.address = {<<{pkt.address}};
    pkt.endpoint = {<<{pkt.endpoint}};
    pkt.crc5 = {<<{pkt.crc5}};
    void'(pkt.pack(driver_token_pkt));
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
    if (req_item.m_pid_type == PidTypeInToken) begin
      get_dut_response(rsp_item);
      seq_item_port.item_done(rsp_item);
      `uvm_info (`gfn, $sformatf("In drive afer In packet : \n %0s", rsp_item.sprint()), UVM_DEBUG)
    end else begin
      seq_item_port.item_done();
    end
  endtask

  task prepare_data_packet(usb20_item req_item, usb20_item rsp_item);
    bit driver_data_pkt[];
    bit comp_data_pkt[];
    // Protect sender from modifications to the request item.
    data_pkt pkt;
    $cast(pkt, req_item.clone());
    pkt.print();
    // Modify each field of the packet to start with the Least Significant Bit (LSB)
    pkt.m_pid_type = pid_type_e'({<<{pkt.m_pid_type}});
    pkt.data = {<<8{pkt.data}};
    pkt.data = {<<{pkt.data}};
    pkt.crc16 = {<<{pkt.crc16}};
    void'(pkt.pack(driver_data_pkt));
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
    `uvm_info(`gfn, $sformatf("\n\nTransfer Type = %s", req_item.m_usb_transfer), UVM_HIGH)
    if (req_item.m_usb_transfer == IsoTrans) begin
      seq_item_port.item_done();
      `uvm_info(`gfn, $sformatf("\n\nTransfer Type = %s", req_item.m_usb_transfer), UVM_HIGH)
    end else begin
      `uvm_info(`gfn, $sformatf("\n\nTransfer Type = %s", req_item.m_usb_transfer), UVM_HIGH)
      get_dut_response(rsp_item);
      seq_item_port.item_done(rsp_item);
    end
  endtask

  task prepare_handshake_packet(usb20_item req_item, usb20_item rsp_item);
    bit driver_handshake_pkt[];
    bit comp_handshake_pkt[];
    // Protect sender from modifications to the request item.
    handshake_pkt pkt;
    $cast(pkt, req_item.clone());
    // Modify each field of the packet to start with the Least Significant Bit (LSB)
    pkt.m_pid_type = pid_type_e'({<<{pkt.m_pid_type}});
    void'(pkt.pack(driver_handshake_pkt));
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

  task prepare_sof_packet(usb20_item req_item, usb20_item rsp_item);
    bit driver_sof_pkt[];
    bit comp_sof_pkt[];
    // Protect sender from modifications to the request item.
    sof_pkt pkt;
    $cast(pkt, req_item.clone());
    pkt.print();
    // Modify each field of the packet to start with the Least Significant Bit (LSB)
    pkt.m_pid_type = pid_type_e'({<<{pkt.m_pid_type}});
    pkt.framecnt = {<<{pkt.framecnt}};
    pkt.crc5 = {<<{pkt.crc5}};
    void'(pkt.pack(driver_sof_pkt));
    // to make complete packet need to attach SYNC at start of packet
    comp_sof_pkt = new[driver_sof_pkt.size() + 8];
    for (int i = 0; i < 8; i++) begin
      comp_sof_pkt[i] = SYNC_PATTERN[i];
    end
    for (int i = 0; i < driver_sof_pkt.size(); i++) begin
      comp_sof_pkt[i + 8] = driver_sof_pkt[i];
    end
    `uvm_info(`gfn, $sformatf("Complete Sof_Packet = %p", comp_sof_pkt), UVM_HIGH)
    drive_pkt(comp_sof_pkt);
    seq_item_port.item_done();
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

  // Bit Stuffing/Unstuffing Task
  // -------------------------------
  task bit_stuffing(input bit packet[], output bit bit_stuff_out[]);
    int consecutive_ones_count = 0;
    bit stuffed[$];
    for (int i = 0; i < packet.size(); i++) begin
      stuffed.push_back(packet[i]);
      if (packet[i] == 1'b1) begin
        consecutive_ones_count = consecutive_ones_count + 1;
        if (consecutive_ones_count >= 6) begin
          consecutive_ones_count = 0;
          stuffed.push_back(1'b0);
        end
      end else consecutive_ones_count = 0;
    end
    bit_stuff_out = stuffed;
  endtask

  // Returns 1 in the event of detecting a bit stuffing error, output is
  // still complete but likely invalid (no bits dropped where the stuffed '0'
  // was expected).
  function bit bit_unstuffing(input bit in[], output bit out[]);
    int consecutive_ones_count = 0;
    bit unstuffed[$];
    bit error = 1'b0;
    for (int i = 0; i < in.size(); i++) begin
      if (consecutive_ones_count >= 6) begin
        if (in[i] == 1'b1) begin
          unstuffed.push_back(in[i]);
          `uvm_info(`gfn, $sformatf("Bit stuffing error at offset %d", i), UVM_LOW)
          error = 1'b1;
        end
        consecutive_ones_count = 0;
      end else unstuffed.push_back(in[i]);
      if (in[i] == 1'b1) consecutive_ones_count = consecutive_ones_count + 1;
      else consecutive_ones_count = 0;
    end
    // Six ones at the end of the packet without a stuffed '0' also constitutes
    // an error. Note that we need not be concerned with 'dribble' (section 7.1.9.1)
    // here because of the direct connection to the USB device.
    if (consecutive_ones_count >= 6) error = 1'b1;
    out = unstuffed;
    return error;
  endfunction

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
        // If the current NRZI bit matches the previous bit, it's a 1.
        decoded_packet[i] = 1'b1;
      end else begin
        // If the current NRZI bit is different from the previous bit, it's a 0.
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
    cfg.bif.drive_p  = 1'b0;
    cfg.bif.drive_n = 1'b0;
    @(posedge cfg.bif.rst_ni);
    cfg.bif.usb_vbus = 1'b0;
    repeat(usb_idle_clk_cycles) @(posedge cfg.bif.usb_clk);
    cfg.bif.usb_vbus = 1'b1;
    bus_reset();
  endtask

  // USB Bus Reset Task
  // -------------------------------
  task bus_reset();
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
  task get_dut_response(ref usb20_item rsp_item);
    bit received_pkt[];
    bit nrzi_out_pkt[];
    bit decoded_received_pkt[];
    int receive_index = 0;
    bit [7:0] received_pid = 0;
    bit bitstuff_err;
    bit use_negedge;
    // TODO: DV should not be stealing access to the driver enable of the DUT and would ideally
    // be able to synchronize to just the USB_P/N signals are they are received.
    `uvm_info(`gfn, "After drive Packet in wait to check usb_dp_en_o signal", UVM_DEBUG)
    wait(cfg.bif.usb_dp_en_o);
    // TODO: Operating on a div 4 clock is inherently fraught and runs into sampling problems;
    // a simple solution would be to use the 4x oversampling and detect the initial transition away
    // from Idle state, then choose an appropriate sampling phase [0,3] on the 4x clock.
    //
    // Here, for now, we just choose the clock edge to sidestep sampling errors.
    // This only works because the div 4 clock is derived from and phase-locked to the 48MHz device
    // clock.
    use_negedge = (cfg.bif.usb_clk === 1'b0);
    `uvm_info(`gfn, $sformatf("use_neg %d clk %d", use_negedge, cfg.bif.usb_clk), UVM_LOW)

    while (cfg.bif.usb_dp_en_o) begin
      if (use_negedge) @(negedge cfg.bif.usb_clk);
      else @(posedge cfg.bif.usb_clk);
      // Detect SE0 signaling which indicates End Of Packet
      if (cfg.bif.usb_p === 1'b0 && cfg.bif.usb_n === 1'b0) break;
      received_pkt = new[received_pkt.size() + 1](received_pkt);
      received_pkt[receive_index] = cfg.bif.usb_p;
      receive_index = receive_index + 1;
    end
    `uvm_info(`gfn, $sformatf("Received Packet = %p", received_pkt), UVM_LOW)
    nrzi_decoder(received_pkt, nrzi_out_pkt);
    `uvm_info(`gfn, $sformatf("NRZI-decoded Packet = %p", nrzi_out_pkt), UVM_LOW)
    bitstuff_err = bit_unstuffing(nrzi_out_pkt, decoded_received_pkt);
    `DV_CHECK_EQ(bitstuff_err, 0, "Bit stuffing error detected");
    `uvm_info(`gfn, $sformatf("Decoded Received Packet = %p", decoded_received_pkt), UVM_LOW)
    // TODO: check that we have enough bits for the PID
    for (int i = 0 ; i < 8; i++) begin
      received_pid[i] = decoded_received_pkt[i + 8];
    end

    // Capture the Packet IDentifier and Packet Type
    rsp_item.m_pid_type = pid_type_e'(received_pid);
    case (rsp_item.m_pid_type)
      // Handshake Packet IDentififers
      PidTypeAck, PidTypeNak, PidTypeStall, PidTypeNyet: rsp_item.m_pkt_type = PktTypeHandshake;
      // Data Packet IDentifiers
      PidTypeData0, PidTypeData1, PidTypeData2, PidTypeMData: rsp_item.m_pkt_type = PktTypeData;
      // Start Of Frame
      PidTypeSofToken: rsp_item.m_pkt_type = PktTypeSoF;
      // Treat everything else as a Token, although some of them are 'Special'
      default: rsp_item.m_pkt_type = PktTypeToken;
    endcase

    // TODO: Temporary code just to lift the received DATA packet content of an IN transaction.
    case (rsp_item.m_pid_type)
      PidTypeData0, PidTypeData1: begin
        // TODO: Ignoring the 16-bits of CRC, and we have possibly captured some additional bit(s)
        // from the EOP (SE0) signaling.
        int unsigned len = (decoded_received_pkt.size() - 32) & ~7;  // integral byte count
        data_pkt data;
        `uvm_create_obj(data_pkt, data)
        data.set_id_info(rsp_item);
        data.m_pkt_type = rsp_item.m_pkt_type;
        data.m_pid_type = rsp_item.m_pid_type;
        data.data = new [len >> 3];
        for (int unsigned i = 0; i < len; i++) begin
          data.data[i >> 3] = data.data[i >> 3] | (decoded_received_pkt[i + 16] << (i & 7));
        end
        rsp_item = data;
        `uvm_info(`gfn, $sformatf("IN packet has length %d bytes", len >> 3), UVM_DEBUG)
      end
      default: begin
        // No other PID type carries a data payload.
      end
    endcase
  endtask
endclass
