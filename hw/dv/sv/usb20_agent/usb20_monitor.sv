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

   bit token_packet[];
   bit data_packet[];
   bit handshake_packet[];
   bit sync_pattern[];
   bit decoded_packet[];
   bit monitored_decoded_packet[];
   bit seo;
   bit [2:0] eop_cnt = 3'b000;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
      usb20_monitor_analysis_port = new("usb20_monitor_analysis_port", this);
      if (!uvm_config_db#(virtual usb20_block_if)::get(this, "*.env.m_usb20_agent*", "bif",cfg.bif))
      begin
        `uvm_fatal(`gfn, "failed to get usb20_block_if handle from uvm_config_db")
      end
  endfunction

  task run_phase(uvm_phase phase);
    forever begin
      collect_trans(phase);
      //collect_data_packet(phase);
      //collect_handshake_packet(phase);
    end
  endtask

  //MONITOR TOKEN_PACKET
  virtual protected task collect_trans(uvm_phase phase);
    //while driving the packet before vbus gets active the reset toggle 2,3 times so below wait
    //conditions waits for the those reset and than it detected the vbus
    wait(cfg.bif.rst_ni);
    wait(~cfg.bif.rst_ni);
    wait(cfg.bif.rst_ni);
    wait(~cfg.bif.rst_ni);
    wait(cfg.bif.rst_ni);
    `uvm_info(`gfn, $sformatf("\n Vbus detected = %b reset = %b", cfg.bif.usb_vbus, cfg.bif.rst_ni),
    UVM_LOW)
    //idle state detetcted here
    wait(cfg.bif.usb_p & ~cfg.bif.usb_n);
    `uvm_info(`gfn, $sformatf("\n Idle State_usb_p Monitored = %b Idle State_usb_n Monitored = %b" ,
    cfg.bif.usb_p, cfg.bif.usb_n), UVM_LOW)
    wait(~cfg.bif.usb_p);
    while (1)begin
      @(posedge cfg.bif.usb_clk) begin
        if(cfg.bif.usb_p == 1'b0 & cfg.bif.usb_n == 1'b0)
        begin
          seo = 1'b1;
          for(int i = 0; i <2; i = i + 1)
          begin
            token_packet = new[token_packet.size()+1](token_packet);
            token_packet[token_packet.size()-1] = cfg.vif.usb_p;
          end
        break;
        end
        else
        begin
          token_packet = new[token_packet.size()+1](token_packet);
          token_packet[token_packet.size()-1] = cfg.vif.usb_p;
        end
      end
    end
    `uvm_info(`gfn, $sformatf("complete monitored token_packet = %p ", token_packet), UVM_LOW)
    bit_destuffing(token_packet);
    `uvm_info(`gfn, $sformatf("Monitored destuffed token_packet: %p", token_packet), UVM_LOW)
    nrzi_decoder(token_packet, monitored_decoded_packet);
    `uvm_info(`gfn, $sformatf("Monitored NRZI decoder token_packet  =%p",
    monitored_decoded_packet), UVM_LOW)
  endtask

  //MONITOR DATA_PACKET
  virtual protected task collect_data_packet(uvm_phase phase);
    wait(cfg.bif.usb_p & ~cfg.bif.usb_n);
    `uvm_info(`gfn, $sformatf("\n After EOP Idle State Monitored"), UVM_LOW)
    wait(~cfg.bif.usb_p);
    while(1)begin
      @(posedge cfg.bif.usb_clk) begin
        if(cfg.bif.usb_p == 1'b0 & cfg.bif.usb_n == 1'b0) begin
          seo = 1;
          for(int i = 0; i <2; i = i + 1)
          begin
            data_packet = new[data_packet.size()+1](data_packet);
            data_packet[data_packet.size()-1] = cfg.vif.usb_p;
          end
        break;
        end
        else
        begin
          data_packet = new[data_packet.size()+1](data_packet);
          data_packet[data_packet.size()-1] = cfg.vif.usb_p;
        end
      end
    end
    `uvm_info(`gfn, $sformatf("Complete Monitored Data_Packet = %p ", data_packet), UVM_LOW)
    bit_destuffing(data_packet);
    `uvm_info(`gfn, $sformatf("Monitored Destuffed Data_Packet: %p", data_packet), UVM_LOW)
    nrzi_decoder(data_packet, monitored_decoded_packet);
    `uvm_info(`gfn, $sformatf("Monitored NRZI Decoder Data_Packet =%p", monitored_decoded_packet),
    UVM_LOW)
  endtask

  //MONITOR HANDSHAKE_PACKET
  virtual protected task collect_handshake_packet(uvm_phase phase);
    wait(cfg.bif.usb_p & ~cfg.bif.usb_n);
    `uvm_info(`gfn, $sformatf("\n After EOP Idle State Monitored"), UVM_LOW)
    wait(~cfg.bif.usb_p);
    while(1) begin
      @(posedge cfg.bif.usb_clk) begin
        if(cfg.bif.usb_p == 1'b0 & cfg.bif.usb_n == 1'b0) begin
          seo = 1;
          for(int i = 0; i <2; i = i + 1)
          begin
            handshake_packet = new[handshake_packet.size()+1](handshake_packet);
            handshake_packet[handshake_packet.size()-1] = cfg.vif.usb_p;
          end
        break;
        end
        else
        begin
          handshake_packet = new[handshake_packet.size()+1](handshake_packet);
          handshake_packet[handshake_packet.size()-1] = cfg.vif.usb_p;
        end
      end
    end
    `uvm_info(`gfn, $sformatf("Complete Monitored Handshake_Packet = %p ", handshake_packet),
    UVM_LOW)
    bit_destuffing(handshake_packet);
    `uvm_info(`gfn, $sformatf("Monitored Destuffed Handshake_Packet: %p", handshake_packet),
    UVM_LOW)
    nrzi_decoder(handshake_packet, monitored_decoded_packet);
    `uvm_info(`gfn, $sformatf("Monitored NRZI Decoder Handshake_Packet =%p",monitored_decoded_packet
    ),UVM_LOW)
  endtask

  //NRZI DECODER
  task nrzi_decoder(input bit nrzi_in[], output bit monitored_decoded_packet[]);
    bit prev_bit = 1'b1;
    monitored_decoded_packet = new[nrzi_in.size()];
    for (int i = 0; i < nrzi_in.size(); i++) begin
      if (nrzi_in[i] == prev_bit) begin
        // If the current NRZI bit matches the previous bit, it's a 0.
        monitored_decoded_packet[i] = 1'b1;
      end
      else
      begin
        // If the current NRZI bit is different from the previous bit, it's a 1.
        monitored_decoded_packet[i] = 1'b0;
      end
      prev_bit = nrzi_in[i];
    end
  endtask

  //BIT DESTUFFING
  task bit_destuffing(input bit packet[]);
    int consecutive_ones_count = 0;
    for (int i = 0; i < packet.size(); i++) begin
      if (packet[i] == 1'b1) begin
        consecutive_ones_count = consecutive_ones_count +1;
        if (consecutive_ones_count == 6) begin
          packet = new[packet.size() - 1](packet);
          i++;
          for (int j = i ; j < packet.size(); j++) begin
            packet[j] = packet[j + 1];
          end
          consecutive_ones_count =0;
        end
      end
      else if (packet[i] ==1'b0) begin
        consecutive_ones_count =0;
      end
    end
  endtask

  virtual task monitor_ready_to_end();
    wait(cfg.bif.rst_ni);
    wait(~cfg.bif.rst_ni);
    wait(cfg.bif.rst_ni);
    wait(~cfg.bif.rst_ni);
    wait(cfg.bif.rst_ni);
    wait(cfg.bif.usb_p & ~cfg.bif.usb_n);
    forever begin
      @(posedge cfg.bif.usb_clk) begin
        if(cfg.bif.usb_p == 1'b0 & cfg.bif.usb_n == 1'b0) begin
          eop_cnt++;
          if (eop_cnt == 3'b110) begin
            ok_to_end = 1;
            eop_cnt = 0;
            break;
          end
        else begin
          ok_to_end = 0;
        end
      end
     end
    end
    `uvm_info(`gfn, $sformatf("ok_to_end: %b", ok_to_end), UVM_LOW)
  endtask : monitor_ready_to_end
endclass
