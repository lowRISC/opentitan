// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class spi_device_driver extends spi_driver;
  `uvm_component_utils(spi_device_driver)
  `uvm_component_new

  virtual task reset_signals();
    forever begin
      @(negedge cfg.vif.rst_n);
      `uvm_info(`gfn, "\n  spi_device_driver in reset progress", UVM_LOW)
      under_reset = 1'b1;
      cfg.vif.sio <= 4'd0;
      @(posedge cfg.vif.rst_n);
      under_reset = 1'b0;
      `uvm_info(`gfn, "\n  spi_device_driver out of reset", UVM_LOW)
    end
  endtask

  virtual task get_and_drive();
    forever begin
      wait(!under_reset);
      seq_item_port.get_next_item(req);
      $cast(rsp, req.clone());
      rsp.set_id_info(req);
      `uvm_info(`gfn, $sformatf("  spi_device_driver: req item:\n%0s", req.sprint()), UVM_HIGH)
      fork
        drive_rx_item(req);
        drive_tx_item(req);
      join
      `uvm_info(`gfn, "  spi_device_driver: item sent", UVM_HIGH)
      seq_item_port.item_done(rsp);
    end
  endtask : get_and_drive

  virtual task drive_rx_item(spi_item item);
    bit [3:0] rx_data;
    cfg.wait_sck_edge(SamplingEdge);
    drive_rx_sio(cfg.spi_mode, rx_data);
  endtask : drive_rx_item

  virtual task drive_tx_item(spi_item item);
    bit [7:0] tx_data;

    // TODO
  endtask : drive_tx_item

  virtual task drive_tx_sio(ref spi_mode_e mode, input bit [3:0] tx_data);
    unique case (mode)
      Single: begin
        cfg.vif.sio[1] = tx_data[1];
      end
      Dual: begin
        cfg.vif.sio[3:2] = 2'bzz;
        cfg.vif.sio[1:0] = tx_data[1:0];
      end
      Quad: begin
        cfg.vif.sio = tx_data;
      end
      Reserve: begin
        cfg.vif.sio = 4'd0;
      end
    endcase
  endtask : drive_tx_sio

  virtual task drive_rx_sio(ref spi_mode_e mode, output bit [3:0] rx_data);
    unique case (mode)
      Single: begin
        rx_data[3:2] = 2'bzz;
        rx_data[1]   = cfg.vif.sio[1];
        rx_data[0]   = 1'bz;
      end
      Dual: begin
        rx_data[3:2] = 2'bzz;
        rx_data[1:0] = cfg.vif.sio[1:0];
      end
      Quad: begin
        rx_data = cfg.vif.sio;
      end
      Reserve: begin
        rx_data = 4'bzzzz;
      end
    endcase
  endtask : drive_rx_sio
  
endclass : spi_device_driver
