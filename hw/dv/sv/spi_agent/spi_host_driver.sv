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
      cfg.vif.mosi <= 1'bx;
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
          #(cfg.sck_period_ps / 2 * 1ps);
          cfg.vif.sck <= ~cfg.vif.sck;
          #(cfg.sck_period_ps / 2 * 1ps);
          if (sck_pulses > 0) sck_pulses--;
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
      cfg.vif.csb <= 1'b0;
      sck_pulses = req.data.size() * 8;

      // for mode 1 and 3, get the leading edges out of the way
      cfg.wait_sck_edge(LeadingEdge);

      // drive data
      for (int i = 0; i < req.data.size(); i++) begin
        logic [7:0] host_byte;
        logic [7:0] device_byte;
        int         which_bit;
        host_byte = req.data[i];
        for (int j = 0; j < 8; j++) begin
          // drive mosi early so that it is stable at the sampling edge
          which_bit = cfg.host_bit_dir ? j : 7 - j;
          cfg.vif.mosi <= host_byte[which_bit];
          // wait for sampling edge to sample miso (half cycle)
          cfg.wait_sck_edge(SamplingEdge);
          which_bit = cfg.device_bit_dir ? j : 7 - j;
          device_byte[which_bit] = cfg.vif.miso;
          // wait for driving edge to complete 1 cycle
          if (i != req.data.size() - 1 || j != 7) cfg.wait_sck_edge(DrivingEdge);
        end
        rsp.data[i] = device_byte;
      end

      wait(sck_pulses == 0);
      cfg.vif.csb <= 1'b1;
      cfg.vif.mosi <= 1'bx;
      `uvm_info(`gfn, "spi_host_driver: item sent", UVM_HIGH)
      seq_item_port.item_done(rsp);
    end
  endtask

endclass
