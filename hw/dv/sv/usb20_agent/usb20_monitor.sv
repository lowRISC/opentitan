// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usb20_monitor extends dv_base_monitor #(
  .ITEM_T (usb20_item),
  .CFG_T  (usb20_agent_cfg),
  .COV_T  (usb20_agent_cov)
);
  `uvm_component_utils(usb20_monitor)

   uvm_analysis_port #(usb20_item) usb20_monitor_analysis_port;

   sof_pkt        m_sof_pkt;
   token_pkt      m_token_pkt;
   data_pkt       m_data_pkt;
   handshake_pkt  m_handshake_pkt;
   typedef bit destuffed_t[];
   bit token_packet[$];
   bit data_packet[$];
   bit handshake_packet[$];
   bit sof_packet[$];
   bit sync_pattern[];
   bit decoded_packet[];
   bit monitored_decoded_packet[];
   bit bit_destuffed[];
   bit [2:0] eop_cnt = 3'b000;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    m_sof_pkt = sof_pkt::type_id::create("m_sof_pkt", this);
    m_token_pkt = token_pkt::type_id::create("m_token_pkt", this);
    m_data_pkt = data_pkt::type_id::create("m_data_pkt", this);
    m_handshake_pkt = handshake_pkt::type_id::create("m_handshake_pkt", this);
    usb20_monitor_analysis_port = new("usb20_monitor_analysis_port", this);
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
    forever begin
      collect_trans(phase);
      collect_data_packet();
      collect_handshake_packet();
    end
  endtask

  // For future use (task written but not used yet)
  // Monitor start of frame packet
  virtual protected task collect_sof_packet();
    typedef bit [34:0] sof_p;
    sof_p sof_result;

    // While driving the packet before vbus gets active the reset toggle 2,3 times so below wait
    // Conditions waits for the those reset and than it detected the vbus
    detect_reset();

    // Idle state detected here
    while(!(cfg.bif.usb_p & ~cfg.bif.usb_n)) @(posedge cfg.bif.usb_clk);
    `uvm_info(`gfn, $sformatf("Idle State_usb_p Monitored = %b Idle State_usb_n Monitored = %b",
                               cfg.bif.usb_p, cfg.bif.usb_n), UVM_DEBUG)
    @(posedge cfg.bif.usb_clk);
    wait(~cfg.bif.usb_p);

    // Collecting usb_p from interface
    @(posedge cfg.bif.usb_clk);
    while (cfg.bif.usb_p || cfg.bif.usb_n) begin
      sof_packet.push_back(cfg.bif.usb_p);
      @(posedge cfg.bif.usb_clk);
    end
    repeat (3) sof_packet.push_back(cfg.bif.usb_p);

    `uvm_info(`gfn, $sformatf("Complete Monitored Sof_Packet = %p", sof_packet), UVM_DEBUG)
    nrzi_decoder(sof_packet, monitored_decoded_packet);
    bit_destuffed = bit_destuffing(monitored_decoded_packet);

    // Bits to binary conversion
    sof_result = sof_p'(bit_destuffed);

    `uvm_info(`gfn, $sformatf("Final Sof Packet = %b", sof_result), UVM_DEBUG)
    m_sof_pkt.m_pid_type = sof_result[9:2];
    `uvm_info(`gfn, $sformatf("Sof Pid = %b", m_sof_pkt.m_pid_type), UVM_DEBUG)
    m_sof_pkt.framecnt = sof_result[20:10];
    `uvm_info(`gfn, $sformatf("Sof framecnt = %b", m_sof_pkt.framecnt), UVM_DEBUG)
    m_sof_pkt.crc5 = sof_result[25:21];
    `uvm_info(`gfn, $sformatf("Sof crc5 = %b", m_sof_pkt.crc5), UVM_DEBUG)
    analysis_port.write(m_sof_pkt);
  endtask

  // Monitor token packet
  virtual protected task collect_trans(uvm_phase phase);
    typedef bit [34:0] token_p;
    token_p token_result;

    detect_reset();
    while(!(cfg.bif.usb_p & ~cfg.bif.usb_n)) @(posedge cfg.bif.usb_clk);
    `uvm_info(`gfn, $sformatf("After EOP Idle State Monitored"), UVM_DEBUG)
    @(posedge cfg.bif.usb_clk);
    wait(~cfg.bif.usb_p);

    // Collecting usb_p from interface
    @(posedge cfg.bif.usb_clk);
    while (cfg.bif.usb_p || cfg.bif.usb_n) begin
      token_packet.push_back(cfg.bif.usb_p);
      @(posedge cfg.bif.usb_clk);
    end
    repeat (3) token_packet.push_back(cfg.bif.usb_p);

    `uvm_info(`gfn, $sformatf("Complete monitored token_packet = %p ", token_packet), UVM_DEBUG)
    nrzi_decoder(token_packet, monitored_decoded_packet);
    bit_destuffed = bit_destuffing(monitored_decoded_packet);

    // Bits to binary conversion
    token_result = token_p'(bit_destuffed);

    `uvm_info(`gfn, $sformatf("Final Token Packet = %b", token_result), UVM_DEBUG)
    m_token_pkt.m_pid_type = token_result[26:19];
    `uvm_info(`gfn, $sformatf("Token Pid = %b", m_token_pkt.m_pid_type), UVM_DEBUG)
    m_token_pkt.address = token_result[18:12];
    `uvm_info(`gfn, $sformatf("Token Address = %b", m_token_pkt.address), UVM_DEBUG)
    m_token_pkt.endpoint = token_result[11:8];
    `uvm_info(`gfn, $sformatf("Token Endpoint = %b", m_token_pkt.endpoint), UVM_DEBUG)
    m_token_pkt.crc5 = token_result[7:3];
    `uvm_info(`gfn, $sformatf("Token Crc5 = %b", m_token_pkt.crc5), UVM_DEBUG)
    analysis_port.write(m_token_pkt);
  endtask

  // Monitor data packet
  virtual protected task collect_data_packet();
    bit [7:0] data_pid;
    bit [7:0] data_temp[];
    bit data[];
    bit [63:0] data_result;
    bit [15:0] data_crc16;
    byte unsigned byte_data[];

    while(!(cfg.bif.usb_p & ~cfg.bif.usb_n)) @(posedge cfg.bif.usb_clk);
    `uvm_info(`gfn, $sformatf("After EOP Idle State Monitored"), UVM_DEBUG)
    @(posedge cfg.bif.usb_clk);
    wait(~cfg.bif.usb_p);

    // Collecting usb_p from interface
    @(posedge cfg.bif.usb_clk);
    while (cfg.bif.usb_p || cfg.bif.usb_n) begin
      data_packet.push_back(cfg.bif.usb_p);
      @(posedge cfg.bif.usb_clk);
    end
    repeat (3) data_packet.push_back(cfg.bif.usb_p);
    `uvm_info(`gfn, $sformatf("Complete Monitored Data_Packet = %p", data_packet), UVM_DEBUG)
    nrzi_decoder(data_packet, monitored_decoded_packet);
    bit_destuffed = bit_destuffing(monitored_decoded_packet);

    // Converting complete packet into transaction level (field wise)
    // Data_PID
    for (int i = 0; i < 8; i++) begin
      data_pid[i] = bit_destuffed[i + 8];
    end
    m_data_pkt.m_pid_type = data_pid;
    `uvm_info(`gfn, $sformatf("Data Pid = %b", m_data_pkt.m_pid_type), UVM_DEBUG)
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
    `uvm_info(`gfn, $sformatf("Data = %p", m_data_pkt.data), UVM_DEBUG)
    // Crc16
    for (int i= 0; i < 16; i = i+1) begin
      data_crc16[i] = bit_destuffed[i + 16 + data.size()];
    end
    m_data_pkt.crc16 = data_crc16;
    `uvm_info(`gfn, $sformatf("Data Crc16 = %b", m_data_pkt.crc16), UVM_DEBUG)
    analysis_port.write(m_data_pkt);
  endtask

  // Monitor handshake packet
  virtual protected task collect_handshake_packet();
    typedef bit [18:0] handshake_p;
    handshake_p handshake_result;

    while(!(cfg.bif.usb_p & ~cfg.bif.usb_n)) @(posedge cfg.bif.usb_clk);
    `uvm_info(`gfn, $sformatf("\n After EOP Idle State Monitored"), UVM_DEBUG)
    @(posedge cfg.bif.usb_clk);
    wait(~cfg.bif.usb_p);

    // Collecting usb_p from interface
    @(posedge cfg.bif.usb_clk);
    while (cfg.bif.usb_p || cfg.bif.usb_n) begin
      handshake_packet.push_back(cfg.bif.usb_p);
      @(posedge cfg.bif.usb_clk);
    end
    repeat (3) handshake_packet.push_back(cfg.bif.usb_p);
    `uvm_info(`gfn, $sformatf("Complete Monitored Handshake_Packet = %p ", handshake_packet),
              UVM_DEBUG)
    nrzi_decoder(handshake_packet, monitored_decoded_packet);
    bit_destuffed = bit_destuffing(monitored_decoded_packet);

    // bits to binary conversion
    handshake_result = handshake_p'(bit_destuffed);

    `uvm_info(`gfn, $sformatf("Final Handshake Packet = %b", handshake_result), UVM_DEBUG)
    m_handshake_pkt.m_pid_type = handshake_result[10:3];
    m_handshake_pkt.m_pid_type = {<<4{m_handshake_pkt.m_pid_type}};
    m_handshake_pkt.m_pid_type = {<<{m_handshake_pkt.m_pid_type}};
    `uvm_info(`gfn, $sformatf("Handshake Pid = %b", m_handshake_pkt.m_pid_type), UVM_DEBUG)
    analysis_port.write(m_handshake_pkt);
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
  function destuffed_t bit_destuffing(bit packet[]);
    int consecutive_ones_count = 0;
    for (int i = 0; i < packet.size(); i++) begin
      if (packet[i] == 1'b1) begin
        consecutive_ones_count = consecutive_ones_count + 1;
        if (consecutive_ones_count == 6) begin
          packet = new[packet.size() - 1](packet);
          i++;
          for (int j = i; j < packet.size(); j++) begin
            packet[j] = packet[j + 1];
          end
          consecutive_ones_count = 0;
        end
      end else if (packet[i] == 1'b0) begin
        consecutive_ones_count = 0;
      end
    end
    `uvm_info(`gfn, $sformatf("Monitored Destuffed Packet = %p", packet), UVM_DEBUG)
    return packet;
  endfunction


  // Reset detection
  task detect_reset();
    bit next_rst_phase = 1'b1;
    @(posedge cfg.bif.usb_clk);
    repeat (4) begin
      while (cfg.bif.rst_ni != next_rst_phase) @(posedge cfg.bif.usb_clk);
    end
    cfg.clk_rst_if_i.wait_for_reset(1, 1);
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
