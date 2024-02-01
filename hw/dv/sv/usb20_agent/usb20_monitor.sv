// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usb20_monitor extends dv_base_monitor #(
  .ITEM_T (usb20_item),
  .REQ_ITEM_T (usb20_item),
  .RSP_ITEM_T (usb20_item),
  .CFG_T  (usb20_agent_cfg),
  .COV_T  (usb20_agent_cov)
);
  `uvm_component_utils(usb20_monitor)

   usb20_item     m_usb20_item;
   sof_pkt        m_sof_pkt;
   token_pkt      m_token_pkt;
   data_pkt       m_data_pkt;
   handshake_pkt  m_handshake_pkt;
   bit packet[$];
   bit sync_pattern[];
   bit decoded_packet[];
   bit monitored_decoded_packet[];
   bit bit_destuffed[$];
   bit [2:0] eop_cnt = 3'b000;
   bit [7:0] packet_type;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    m_sof_pkt = sof_pkt::type_id::create("m_sof_pkt", this);
    m_token_pkt = token_pkt::type_id::create("m_token_pkt", this);
    m_data_pkt = data_pkt::type_id::create("m_data_pkt", this);
    m_handshake_pkt = handshake_pkt::type_id::create("m_handshake_pkt", this);
    if (!uvm_config_db#(virtual usb20_block_if)::get(this, "*.env.m_usb20_agent*", "bif",
                                                     cfg.bif)) begin
      `uvm_fatal(`gfn, "failed to get usb20_block_if handle from uvm_config_db")
    end
    if (!uvm_config_db#(virtual clk_rst_if)::get(this, "*.env", "clk_rst_vif",
                                                 cfg.clk_rst_if_i)) begin
      `uvm_fatal(`gfn, "failed to get clk_rst_if handle from uvm_config_db")
    end
  endfunction

  task run_phase(uvm_phase phase);
    detect_reset();
    forever begin
      collect_trans();
    end
  endtask

//-----------------------------------------Collect Trans------------------------------------------//
  virtual protected task collect_trans();
    bit use_negedge;

    // Wait until bus becomes Idle
    while(!(cfg.bif.usb_p & ~cfg.bif.usb_n)) @(posedge cfg.bif.usb_clk);
    @(posedge cfg.bif.usb_clk);
    // Departure from Idle state detected here; this is assumed to be the start of a packet.
    wait(~cfg.bif.usb_p);

    // TODO: Operating on a div 4 clock is inherently fraught and runs into sampling problems;
    // a simple solution would be to use the 4x oversampling and detect the initial transition away
    // from Idle state, then choose an appropriate sampling phase [0,3] on the 4x clock.
    //
    // Here, for now, we just choose the clock edge to sidestep sampling errors.
    // This only works because the div 4 clock is derived from and phase-locked to the 48MHz device
    // clock.
    use_negedge = (cfg.bif.usb_clk === 1'b1);
    `uvm_info(`gfn, $sformatf("use_neg %d clk %d", use_negedge, cfg.bif.usb_clk), UVM_LOW)
    if (use_negedge) @(negedge cfg.bif.usb_clk);
    else @(posedge cfg.bif.usb_clk);

    // Collecting usb_p from interface
    while (cfg.bif.usb_p || cfg.bif.usb_n) begin
      packet.push_back(cfg.bif.usb_p);
      if (use_negedge) @(negedge cfg.bif.usb_clk);
      else @(posedge cfg.bif.usb_clk);
    end
    // TODO: this does not even check the EOP!
    repeat (3) packet.push_back(cfg.bif.usb_p);

    `uvm_info(`gfn, $sformatf("Complete monitored packet = %p ", packet), UVM_DEBUG)
    nrzi_decoder(packet, monitored_decoded_packet);
    bit_destuffing(monitored_decoded_packet, bit_destuffed);
    classifies_packet();
    packet.delete();
  endtask

//----------------------------------------Classifies Trans----------------------------------------//
  virtual task classifies_packet();
    for (int i = 0; i < 8; i++) begin
    packet_type[i] = bit_destuffed[i + 8];
    end
    `uvm_info(`gfn, $sformatf(".......Packet PID = %b ", packet_type), UVM_DEBUG)
    case (packet_type)
      PidTypeOutToken: token_packet();
      PidTypeInToken: token_packet();
      PidTypeSetupToken: token_packet();
      PidTypeSofToken: sof_packet();
      PidTypeData0: data_packet();
      PidTypeData1: data_packet();
      PidTypeAck: handshake_packet();
      PidTypeNak: handshake_packet();
      PidTypeStall: handshake_packet();
      default: invalid_packet_pid();
    endcase
  endtask

//-------------------------------------------SOF Packet-------------------------------------------//
  virtual task sof_packet();
    typedef bit [34:0] sof_p;
    sof_p sof_result;

    // bits to binary conversion
    sof_result = sof_p'(bit_destuffed);
    m_sof_pkt.m_pid_type = pid_type_e'(packet_type);
    m_sof_pkt.framecnt = {<<{sof_result[18:8]}};
    m_sof_pkt.crc5 = {<<{sof_result[7:3]}};
    req_analysis_port.write(m_sof_pkt);
  endtask

//------------------------------------------Token Packet------------------------------------------//
  virtual task token_packet();
    typedef bit [34:0] token_p;
    token_p token_result;

    // bits to binary conversion
    token_result = token_p'(bit_destuffed);
    m_token_pkt.m_pid_type =  pid_type_e'(packet_type);
    m_token_pkt.address = {<<{token_result[18:12]}};
    m_token_pkt.endpoint = {<<{token_result[11:8]}};
    m_token_pkt.crc5 = {<<{token_result[7:3]}};
    req_analysis_port.write(m_token_pkt);
  endtask

//------------------------------------------Data Packet-------------------------------------------//
  virtual task data_packet();
    bit [7:0] data_pid;
    bit [7:0] data_temp[];
    bit data[];
    bit [6:0] size;
    bit [63:0] data_result;
    bit [15:0] data_crc16;
    byte unsigned byte_data[];

    // Converting complete packet into transaction level (field wise)
    // Data_PID
    m_data_pkt.m_pid_type = pid_type_e'(packet_type);
    // Data_in_bits
    for (int i = 0 ; i < bit_destuffed.size() - 35; i++) begin
      data = new[data.size() + 1](data);
      data[i] = bit_destuffed[i + 16];
    end
    data = {<<8{data}};
    data = {<<{data}};
    // Bits_to_byte conversion of data
    byte_data = {>>byte{data}};
    m_data_pkt.data = byte_data;
    // Crc16
    for (int i= 0; i < 16; i = i+1) begin
      data_crc16[i] = bit_destuffed[i + 16 + data.size()];
    end
    m_data_pkt.crc16 = data_crc16;
     if (cfg.bif.usb_dp_en_o) rsp_analysis_port.write(m_data_pkt);
    else req_analysis_port.write(m_data_pkt);
  endtask

//----------------------------------------Handshake Packet----------------------------------------//
  virtual task handshake_packet();
    typedef bit [18:0] handshake_p;
    handshake_p handshake_result;

    // bits to binary conversion
    handshake_result = handshake_p'(bit_destuffed);
    m_handshake_pkt.m_pid_type = pid_type_e'(packet_type);
    if (cfg.bif.usb_dp_en_o) rsp_analysis_port.write(m_handshake_pkt);
    else req_analysis_port.write(m_handshake_pkt);
  endtask

  //----------------------------------------Invalid Packet----------------------------------------//
  virtual task invalid_packet_pid();
    typedef bit [7:0] invalid_pid_p;
    invalid_pid_p invalid_pid_result;
    int unsigned size;
    size = $size(bit_destuffed);
    `uvm_info(`gfn, $sformatf("packet size = %d", size), UVM_DEBUG)
    if (size == 35) token_packet();
    else if (size == 19) handshake_packet();
    else data_packet();
  endtask

  // NRZI decoder
  task nrzi_decoder(input bit nrzi_in[], output bit monitored_decoded_packet[]);
    bit prev_bit = 1'b1;
    monitored_decoded_packet = new[nrzi_in.size()];
    for (int i = 0; i < nrzi_in.size(); i++) begin
      if (nrzi_in[i] == prev_bit) begin
        // If the current NRZI bit matches the previous bit, it's a 0.
        monitored_decoded_packet[i] = 1'b1;
      end else begin
        // If the current NRZI bit is different from the previous bit, it's a 1.
        monitored_decoded_packet[i] = 1'b0;
      end
      prev_bit = nrzi_in[i];
    end
    `uvm_info(`gfn, $sformatf("Monitored NRZI Decoded Packet = %p", monitored_decoded_packet),
              UVM_DEBUG)
  endtask

  // bit destuffing
  task bit_destuffing (input bit packet[], output bit packet_destuffed[$]);
    int consecutive_ones_count = 0;
    int i;
    for (i = 0; i < packet.size(); i++) begin
      if (packet[i] == 1'b1) begin
        consecutive_ones_count = consecutive_ones_count + 1;
        if (consecutive_ones_count == 6) begin
          if(i <= packet.size()) begin
            packet_destuffed.push_back(packet[i]);
            i += 2; // Skip the next bit as it was part of the stuffing
            consecutive_ones_count = 0;
            if (packet[i] == 1'b1)
              consecutive_ones_count = consecutive_ones_count + 1;
          end else break;
        end
      end else begin
        consecutive_ones_count = 0;
      end
      if(i <= packet.size()) begin
        packet_destuffed.push_back(packet[i]); // Add the current bit to the destuffed packet
      end
    end
    `uvm_info(`gfn, $sformatf("Monitored Destuffed Packet = %p", packet_destuffed), UVM_DEBUG)
  endtask

  // Reset detection
  task detect_reset();
    bit next_rst_phase = 1'b1;
    @(posedge cfg.bif.usb_clk);

    while (cfg.bif.rst_ni != next_rst_phase) @(posedge cfg.bif.usb_clk);

    // Initially we have have only posedge so assigning 0 to negedge bit because it never detects
    // the negedge of the clk.
    cfg.clk_rst_if_i.wait_for_reset(0, 1);
  endtask

  virtual task monitor_ready_to_end();
    detect_reset();
    wait(cfg.bif.usb_p & ~cfg.bif.usb_n);
    while(!(cfg.bif.usb_p & ~cfg.bif.usb_n)) @(posedge cfg.bif.usb_clk)
    forever begin
      @(posedge cfg.bif.usb_clk);
      if (~cfg.bif.usb_p & ~cfg.bif.usb_n) begin
        eop_cnt++;
        if (eop_cnt == 3'b110) begin
          ok_to_end = 1;
          eop_cnt = 0;
          break;
        end else begin
          ok_to_end = 0;
        end
      end
    end
    `uvm_info(`gfn, $sformatf("ok_to_end = %b", ok_to_end), UVM_DEBUG)
  endtask : monitor_ready_to_end
endclass
