// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/*class usb20_driver extends uvm_driver #(usb20_item);
        `uvm_component_utils(usb20_driver)


 function new (string name, uvm_component parent);
                super.new(name, parent);
 endfunction*/
class usb20_driver extends dv_base_driver #(usb20_item, usb20_agent_cfg);
  `uvm_component_utils(usb20_driver)

  `uvm_component_new
   virtual usb20_if vif;
   usb20_agent_cfg cfg;

   token_pkt tpk;
   data_pkt dpk;
   handshake_pkt hpk;

   bit clk_en;
   bit token_pkt[];
   bit comp_token_pkt[];
   bit data_pkt[];
   bit handshake_pkt[];
   bit [7:0] pid_temp;
   bit [6:0] address_temp;
   bit [3:0] enDpoint_temp;
   bit [4:0] crc_temp;
   bit [23:0] nrzi_out = 0;

   localparam bit [7:0] SYNC_PATTERN = 8'b01010100;
   localparam bit [1:0] EOP = 2'b00;



  // the base class provides the following handles for use:
  // usb20_agent_cfg: cfg




  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
   if (!uvm_config_db#(virtual usb20_if)::get(this, "*.env.m_usb20_agent*", "vif", cfg.vif)) begin
      `uvm_fatal(`gfn, "failed to get usb20_if handle from uvm_config_db")
    end

  endfunction

  virtual task run_phase(uvm_phase phase);
    // base class forks off reset_signals() and get_and_drive() tasks
    super.run_phase(phase);
     cfg.vif.usb_vbus = 1'b1;
     @(posedge cfg.vif.rst);
    fork
         clk_divider();
         begin
         forever begin
         //drive_item();
         reset_signals();
         get_and_drive();
         #1;
         end
        end
   join_none
  endtask


  //DRIVE PACKET
  virtual task get_and_drive();
   usb20_item seq_item;
   bit nrzi_out[];
        //usb_clk_rst_if.set_active(1'b1, 1'b0);
        $display(" Drive functions get_and_drive");
         if( cfg.if_mode == Host)
        seq_item_port.get_next_item(seq_item);
        $display(" Drive functions  after get seq item");
        seq_item.print();
/////////////////////////////////////////////////////////////////////////////////////////////
                            //token packet
/////////////////////////////////////////////////////////////////////////////////////////////
        if (seq_item.type1==token) begin
          $cast(tpk, seq_item);
          tpk.pack(token_pkt);
          tpk.print();
          $display("time=%0t pid=%0b address=%0b endpoint=%0b crc=%b", $time, tpk.pid, tpk.address,tpk.endpoint, tpk.crc5);
          $display("time=%0t Driver token_packet=%p", $time, token_pkt);
        end
        //shifted token_pkt LSB to MSB
        for (int i = 0; i < 24; i = i+1)begin
        token_pkt[i] = {token_pkt[(23-i) % 24]};
        end
        $display("time=%0t Driver token_packet=%p", $time, token_pkt);

        bit_stuffing(token_pkt);
        nrzi_encoder(token_pkt,nrzi_out);
        sync_pattern();


        //foreach(token_pkt[i])begin
        for (int i = 0; i < 24; i = i+1)begin
        @(posedge cfg.vif.clk)
        wait(clk_en)
                      cfg.vif.usb_Dp =  token_pkt[i];
                      cfg.vif.usb_Dn = ~token_pkt[i];
          $display("time=%0t bit=%0d packed_Dp=%0b packed_Dn=%0b", $time, i,cfg.vif.usb_Dp,cfg.vif.usb_Dn);
         end
       eop();
       seq_item_port.item_done();
  endtask

  virtual task sync_pattern();
        for (int i = 0; i <= 7; i = i+1) begin
            @(posedge cfg.vif.clk)
          wait(clk_en);
          cfg.vif.usb_Dp = SYNC_PATTERN[7-i];
          cfg.vif.usb_Dn = ~SYNC_PATTERN[7-i];
          $display("time=%0t bit=%0d packed_Dp=%0b packed_Dn=%0b", $time, i,cfg.vif.usb_Dp,cfg.vif.usb_Dn);
        end
  endtask

  //EOP
  virtual task eop();
        for (int i = 0; i < 2; i = i+1) begin
            @(posedge cfg.vif.clk)
          wait(clk_en);
            cfg.vif.usb_Dp = EOP[i];
            cfg.vif.usb_Dn = ~EOP[i];
            $display("time=%0t bit=%0d packed_Dp=%0b packed_Dn=%0b", $time, i,cfg.vif.usb_Dp,cfg.vif.usb_Dn);
         end
  endtask


  virtual task bit_stuffing(input bit packet[]);
    bit consecutive_ones_count = 0;

    for (int i = 0; i < packet.size(); i++) begin
      if (packet[i] == 1'b1)
        consecutive_ones_count++;
      else
        consecutive_ones_count = 1'b0;

        if (consecutive_ones_count == 6)
          packet[i] = {packet[i],1'b0};
        else
          packet[i] = packet[i];
    end
      $display("time=%0t bit_stuffing=%p ", $time, packet);
  endtask


  virtual task nrzi_encoder(input bit packet[], output bit nrzi_out[]);
    nrzi_out = new[packet.size()] ;

    for (int i = 0 ; i < packet.size(); i++) begin
      if (packet[i] == packet[i+1]) begin
        nrzi_out[i] = 1;
      end
      else begin
        nrzi_out[i] = 0;
      end
    end
    $display("time=%0t nrz_encoded=%p", $time, nrzi_out);
  endtask


  //Enable signal drive
  virtual task clk_divider ();
      bit [1:0]cnt;
   //clk_enable logic
      while(1)begin
       @(posedge cfg.vif.clk)
       cnt = cnt + 1;
       if (cnt == 2'b11)
         clk_en = 1'b1;
       else
         clk_en = 1'b0;
        $display ( " In clk _divider task");
      end
      //$display("time=%0t clock_enable: %b",$time, clk_en);

  endtask

  // reset signals
  virtual task reset_signals();
     $display ( " in reset_signals task");
forever begin
      @(negedge cfg.vif.rst);
      `uvm_info(`gfn, "\ndriver in reset progress", UVM_DEBUG)
      release_bus();
      @(posedge cfg.vif.rst);
      `uvm_info(`gfn, "\ndriver out of reset", UVM_DEBUG)
    end
  endtask

  virtual task release_bus();
    `uvm_info(`gfn, "Driver released the bus", UVM_HIGH)
    // JDON: compared to tb connection, this is wrong.
    //    cfg.vif.usb_dp_o = 1'b1;
    //    cfg.vif.usb_dn_o = 1'b0;
    // I initialize these for the temporary.
    // feel free to modify when it is necessary.
    // without this init, you will see assertion failure.
    cfg.vif.usb_dp_i = 1'b1;
    cfg.vif.usb_dn_i = 1'b0;
    cfg.vif.usb_rx_d_i = 0;
    cfg.vif.usb_sense_i = 0;
  endtask : release_bus

endclass
