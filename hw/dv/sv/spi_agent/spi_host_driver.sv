// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class spi_host_driver extends spi_driver;
  `uvm_component_utils(spi_host_driver)
  `uvm_component_new

  uint sck_pulses = 0;

  virtual task run_phase(uvm_phase phase);
    fork
      super.run_phase(phase);
      gen_sck();
    join
  endtask

  // Resets signals
  virtual task reset_signals();
    forever begin
      @(negedge cfg.vif.rst_n);
      under_reset = 1'b1;
      cfg.vif.sck <= cfg.sck_polarity[0];
      cfg.vif.sio <= 'hz;
      cfg.vif.csb <= 'hF;
      sck_pulses = 0;
      @(posedge cfg.vif.rst_n);
      under_reset = 1'b0;
    end
  endtask

  // generate sck
  task gen_sck();
    @(posedge cfg.vif.rst_n);
    fork
      forever begin
        if (sck_pulses > 0 || cfg.sck_on) begin
          cfg.vif.sck <= ~cfg.vif.sck;
          #((cfg.sck_period_ps / 2 + get_rand_extra_delay_ns_btw_sck() * 1000) * 1ps);
          cfg.vif.sck <= ~cfg.vif.sck;
          #((cfg.sck_period_ps / 2 + get_rand_extra_delay_ns_btw_sck() * 1000) * 1ps);
          if (sck_pulses > 0) sck_pulses--;
          // dly after a word transfer is completed
          if (sck_pulses % 32 == 0) #(get_rand_extra_delay_ns_btw_word() * 1ns);
        end else begin
          @(cfg.sck_on, sck_pulses);
          if (sck_pulses > 0) begin
            // drive half cycle first
            cfg.vif.sck <= cfg.sck_polarity[0];
            #(cfg.sck_period_ps / 2 * 1ps);
          end
        end
        cfg.vif.sck_pulses = sck_pulses;
      end
      forever begin
        @(cfg.sck_polarity[0]);
        cfg.vif.sck_polarity = cfg.sck_polarity[0];
        if (sck_pulses == 0) cfg.vif.sck <= cfg.sck_polarity[0];
      end
      forever begin
        @(cfg.sck_phase[0]);
        cfg.vif.sck_phase = cfg.sck_phase[0];
      end
    join
  endtask : gen_sck

  task get_and_drive();
    forever begin
      seq_item_port.get_next_item(req);
      $cast(rsp, req.clone());
      rsp.set_id_info(req);
      `uvm_info(`gfn, $sformatf("spi_host_driver: rcvd item:\n%0s", req.sprint()), UVM_HIGH)
      case (req.item_type)
        SpiTransNormal:   drive_normal_item();
        SpiTransSckNoCsb: drive_sck_no_csb_item();
        SpiTransCsbNoSck: drive_csb_no_sck_item();
        SpiFlashTrans:    drive_flash_item();
      endcase
      `uvm_info(`gfn, "spi_host_driver: item sent", UVM_HIGH)
      seq_item_port.item_done(rsp);
    end
  endtask

  task issue_data(bit [7:0] transfer_data[$]);
    for (int i = 0; i < transfer_data.size(); i++) begin
      bit [7:0] host_byte;
      bit [7:0] device_byte;
      int       which_bit;
      bit [3:0] num_bits;
      if (cfg.partial_byte == 1) begin
        num_bits = cfg.bits_to_transfer;
      end else begin
        num_bits = 8;
      end
      host_byte = transfer_data[i];
      for (int j = 0; j < num_bits; j++) begin
        // drive sio early so that it is stable at the sampling edge
        which_bit = cfg.host_bit_dir ? j : 7 - j;
        cfg.vif.sio[0] <= host_byte[which_bit];
        // wait for sampling edge to sample sio (half cycle)
        cfg.wait_sck_edge(SamplingEdge);
        which_bit = cfg.device_bit_dir ? j : 7 - j;
        device_byte[which_bit] = cfg.vif.sio[1];
        // wait for driving edge to complete 1 cycle
        if (i != transfer_data.size() - 1 || j != (num_bits - 1)) cfg.wait_sck_edge(DrivingEdge);
      end
      rsp.data[i] = device_byte;
    end
  endtask

  task drive_normal_item();
    cfg.vif.csb[cfg.csb_sel] <= 1'b0;
    if ((req.data.size() == 1) && (cfg.partial_byte == 1)) begin
      sck_pulses = cfg.bits_to_transfer;
    end else begin
      sck_pulses = req.data.size() * 8;
    end

    // for mode 1 and 3, get the leading edges out of the way
    cfg.wait_sck_edge(LeadingEdge);

    // drive data
    issue_data(req.data);

    wait(sck_pulses == 0);
    if (cfg.csb_consecutive == 0) begin
      cfg.vif.csb[cfg.csb_sel] <= 1'b1;
      cfg.vif.sio[0] <= 1'bx;
    end
  endtask

  task drive_flash_item();
    bit [7:0] cmd_addr_bytes[$];

    `uvm_info(`gfn, $sformatf("Driving flash item: \n%s", req.sprint()), UVM_MEDIUM)
    cfg.vif.csb[cfg.csb_sel] <= 1'b0;

    cmd_addr_bytes = {req.opcode, req.address_q};
    sck_pulses = cmd_addr_bytes.size() * 8 + req.dummy_cycles;
    if (req.write_command) begin
      `DV_CHECK_EQ(req.num_lanes, 1)
      sck_pulses += req.payload_q.size * 8;
    end else begin
      `DV_CHECK_EQ(req.payload_q.size, 0)
      sck_pulses += req.read_size * (8 / req.num_lanes);
    end

    // for mode 1 and 3, get the leading edges out of the way
    cfg.wait_sck_edge(LeadingEdge);

    // driver cmd and address
    issue_data(cmd_addr_bytes);

    // align to DrivingEdge, if the item has more to send
    if (req.dummy_cycles > 0 || req.payload_q.size > 0 ) cfg.wait_sck_edge(DrivingEdge);
    cfg.vif.sio <= 'dz;

    repeat (req.dummy_cycles) begin
      cfg.wait_sck_edge(DrivingEdge);
    end
    // drive data
    if (req.write_command) begin
      issue_data(req.payload_q);
    end else begin
      repeat (req.read_size) begin
        logic [7:0] data;
        cfg.read_flash_byte(.num_lanes(req.num_lanes), .is_device_rsp(1), .data(data));
        rsp.payload_q.push_back(data);
      end
      `uvm_info(`gfn, $sformatf("collect read data for flash: 0x%p", rsp.payload_q), UVM_MEDIUM)
    end

    wait(sck_pulses == 0);
    cfg.vif.csb[cfg.csb_sel] <= 1'b1;
    cfg.vif.sio <= 'dx;
  endtask

  task drive_sck_no_csb_item();
    repeat (req.dummy_clk_cnt) begin
      #($urandom_range(1, 100) * 1ns);
      cfg.vif.sck <= ~cfg.vif.sck;
    end
    cfg.vif.sck <= cfg.sck_polarity[0];
    #1ps; // make sure sck and csb (for next item) not change at the same time
  endtask

  task drive_csb_no_sck_item();
    cfg.vif.csb[cfg.csb_sel] <= 1'b0;
    #(req.dummy_sck_length_ns * 1ns);
    cfg.vif.csb[cfg.csb_sel] <= 1'b1;
  endtask

  function uint get_rand_extra_delay_ns_btw_sck();
    if (cfg.en_extra_dly_btw_sck && ($urandom % 100) < cfg.extra_dly_chance_pc_btw_sck) begin
      return $urandom_range(cfg.min_extra_dly_ns_btw_sck, cfg.max_extra_dly_ns_btw_sck);
    end else begin
      return 0;
    end
  endfunction

  function uint get_rand_extra_delay_ns_btw_word();
    if (cfg.en_extra_dly_btw_word && ($urandom % 100) < cfg.extra_dly_chance_pc_btw_word) begin
      return $urandom_range(cfg.min_extra_dly_ns_btw_word, cfg.max_extra_dly_ns_btw_word);
    end else begin
      return 0;
    end
  endfunction

endclass
