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
      cfg.vif.sck <= cfg.sck_polarity;
      cfg.vif.csb <= 1'b1;
      cfg.vif.sdi <= 1'bx;
      sck_pulses = 0;
      @(posedge cfg.vif.rst_n);
      under_reset = 1'b0;
    end
  endtask

  // generate sck
  task gen_sck();
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
            cfg.vif.sck <= cfg.sck_polarity;
            #(cfg.sck_period_ps / 2 * 1ps);
          end
        end
        cfg.vif.sck_pulses = sck_pulses;
      end
      forever begin
        @(cfg.sck_polarity);
        cfg.vif.sck_polarity = cfg.sck_polarity;
        if (sck_pulses == 0) cfg.vif.sck <= cfg.sck_polarity;
      end
      forever begin
        @(cfg.sck_phase);
        cfg.vif.sck_phase = cfg.sck_phase;
      end
    join
  endtask

  task get_and_drive();
    forever begin
      seq_item_port.get_next_item(req);
      $cast(rsp, req.clone());
      rsp.set_id_info(req);
      `uvm_info(`gfn, $sformatf("spi_host_driver: rcvd item:\n%0s", req.sprint()), UVM_HIGH)
      case (req.item_type)
        SpiTransNormal:   drive_normal_item();
        SpiTransSckNoCsb: drive_sck_no_csb_item();
        SpiTransCsbNoScb: drive_csb_no_sck_item();
      endcase
      `uvm_info(`gfn, "spi_host_driver: item sent", UVM_HIGH)
      seq_item_port.item_done(rsp);
    end
  endtask

  task drive_normal_item();
    cfg.vif.csb <= 1'b0;
    sck_pulses = req.data.size() * 8;

    // for mode 1 and 3, get the leading edges out of the way
    cfg.wait_sck_edge(LeadingEdge);

    // drive data
    for (int i = 0; i < req.data.size(); i++) begin
      bit [7:0] host_byte;
      bit [7:0] device_byte;
      int       which_bit;
      host_byte = req.data[i];
      for (int j = 0; j < 8; j++) begin
        // drive sdi early so that it is stable at the sampling edge
        which_bit = cfg.host_bit_dir ? j : 7 - j;
        cfg.vif.sdi <= host_byte[which_bit];
        // wait for sampling edge to sample sdo (half cycle)
        cfg.wait_sck_edge(SamplingEdge);
        which_bit = cfg.device_bit_dir ? j : 7 - j;
        device_byte[which_bit] = cfg.vif.sdo;
        // wait for driving edge to complete 1 cycle
        if (i != req.data.size() - 1 || j != 7) cfg.wait_sck_edge(DrivingEdge);
      end
      rsp.data[i] = device_byte;
    end

    wait(sck_pulses == 0);
    cfg.vif.csb <= 1'b1;
    cfg.vif.sdi <= 1'bx;
  endtask

  task drive_sck_no_csb_item();
    repeat (req.dummy_clk_cnt) begin
      #($urandom_range(1, 100) * 1ns);
      cfg.vif.sck <= ~cfg.vif.sck;
    end
    cfg.vif.sck <= cfg.sck_polarity;
    #1ps; // make sure sck and csb (for next item) not change at the same time
  endtask

  task drive_csb_no_sck_item();
    cfg.vif.csb <= 1'b0;
    #(req.dummy_sck_length_ns * 1ns);
    cfg.vif.csb <= 1'b1;
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
