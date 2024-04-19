// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usb20_driver extends dv_base_driver #(usb20_item, usb20_agent_cfg);
  `uvm_component_utils(usb20_driver)

  `uvm_component_new

  // These delays are in terms of bit intervals
  int usb_rst_time = 100_000;  // upto 10ms
  int usb_idle_clk_cycles = 5;
  int usb_pwr_good_clk_cycles = 100;  // arbitrary short delay post-VBUS assertion.

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
      device_response(rsp_item);
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
    if (req_item.m_usb_transfer == IsoTrans) begin
      seq_item_port.item_done();
    end else begin
      device_response(rsp_item);
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

  // Drive the USB to the given state for a single bit interval.
  task drive_bit_interval(bit dp, bit dn);
    @(posedge cfg.bif.clk_i)
    cfg.bif.drive_p = dp;
    cfg.bif.drive_n = dn;
    @(posedge cfg.bif.clk_i);
    @(posedge cfg.bif.clk_i);
    @(posedge cfg.bif.clk_i);
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
      drive_bit_interval(nrzi_out[i], ~nrzi_out[i]);
    end
    end_of_packet();
  endtask

  // EOP Task
  // -------------------------------
  task end_of_packet();
    if (~cfg.single_bit_SE0) begin
      for (int j = 0; j < 2; j++) begin
        drive_bit_interval(EOP[j], EOP[j]);
      end
    end else begin
       drive_bit_interval(EOP[0], EOP[0]);
    end
    `uvm_info(`gfn, "\n After EOP Idle state", UVM_DEBUG)
    drive_bit_interval(1'b1, 1'b0);
  endtask

  // Bit Stuffing/Unstuffing Task
  // -------------------------------
  task bit_stuffing(input bit packet[], output bit bit_stuff_out[]);
    int consecutive_ones_count = 0;
    bit stuffed[$];
   if (~cfg.usb_bitstuff_error) begin
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
   end else
     bit_stuff_out = packet;
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
    // Bus is unpowered and inactive.
    cfg.bif.drive_vbus = 1'b0;
    cfg.bif.usb_rx_d_i = 1'b0;
    cfg.bif.drive_p  = 1'b0;
    cfg.bif.drive_n = 1'b0;
    @(posedge cfg.bif.rst_ni);
    if (cfg.bif.active) begin
      // Idle period post DUT reset.
      repeat (usb_idle_clk_cycles)
        drive_bit_interval(1'b0, 1'b0);
      // TODO: the generation of Bus Reset on the USB shall probably want to become a sequence item,
      // so that it my be done on demand during sequences, and to prevent it interfering with other
      // test sequences.
      cfg.bif.drive_vbus = 1'b1;
      repeat (usb_pwr_good_clk_cycles)
        drive_bit_interval(1'b1, 1'b0);
      bus_reset();
    end
  endtask

  // USB Bus Reset Task
  // -------------------------------
  task bus_reset();
    // Waitfor device active state
    `DV_SPINWAIT(wait(cfg.bif.usb_dp_pullup_o);, "timeout waiting for usb_pullup", 500_000)
    // Reset bus or drive 0 on both DP and DN for 10ms
    repeat (usb_rst_time)
      drive_bit_interval(1'b0, 1'b0);
    `uvm_info(`gfn, "Reset for 10ms completed", UVM_DEBUG)
    // After reset change state to IDLE
    repeat(usb_idle_clk_cycles)
      drive_bit_interval(1'b1, 1'b0);
  endtask

  // Get_DUT_Response
  // -------------------------------
  // This task verifies the device status following the transmission of an OUT packet or IN token.
  // Upon receiving the IN token/OUT packet, the device is expected to initiate a response.
  // This task monitors whether the device initiates the response in the form of a
  // handshake or data packet within the specified timeout period.
  // If no response is detected within timeout frame that is 18 bit times(from section 7.1.19.1),
  // it send timeout response to sequence.
  task device_response(ref usb20_item rsp_item);
    bit timed_out = 1'b0;
    `uvm_info(`gfn, "After drive Packet in wait to check usb_dp_en_o signal", UVM_LOW)
    fork begin : isolation_fork
      fork
        begin
          repeat (18) begin
            repeat (4) @(posedge cfg.bif.clk_i);
            if (cfg.bif.usb_dp_en_o) break;
          end
          if (!cfg.bif.usb_dp_en_o) begin
            timed_out = 1'b1;
            disable get_device_response;
          end
        end
        get_device_response(rsp_item);
      join
      if (timed_out) begin
        // this bit will indicate that device didn't repond within timeout period.
        cfg.time_out = 1'b1;
      end
    end join
  endtask

  task get_device_response(ref usb20_item rsp_item);
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
    while (cfg.bif.usb_dp_en_o) begin
      @(posedge cfg.bif.clk_i);
      @(posedge cfg.bif.clk_i);
      // Detect SE0 signaling which indicates End Of Packet
      if (cfg.bif.usb_p === 1'b0 && cfg.bif.usb_n === 1'b0) break;
      received_pkt = new[received_pkt.size() + 1](received_pkt);
      received_pkt[receive_index] = cfg.bif.usb_p;
      receive_index = receive_index + 1;
      @(posedge cfg.bif.clk_i);
      @(posedge cfg.bif.clk_i);
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
