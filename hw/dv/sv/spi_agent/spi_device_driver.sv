// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// The spi_device_driver responds to bus transactions initiated by a SPI host,
// and its responses depend on cfg.spi_func_mode.
//
// For SpiModeGeneric, the driver waits for CSB to be asserted, then drives
// the contents of spi_item.data sequentially, timed with the SPI host's clock
// output.
//
// For SpiModeFlash, the spi_item must be submitted at exactly the moment when
// the driver is to begin driving the response. The driver sends the contents
// of spi_item.payload_q sequentially, timed with the SPI host's clock output.
// Note that spi_device_driver does NOT observe the command, address, or dummy
// cycles+read_pipeline delay, and it assumes those phases have already passed.
// For this mode, spi_device_driver is anticipated to be used in conjunction with the
// spi_monitor's req_analysis_port, which writes a spi_item into the
// spi_sequencer's connected req_analysis_fifo at the moment those phases have
// completed.
class spi_device_driver extends spi_driver;
  `uvm_component_utils(spi_device_driver)
  `uvm_component_new

  bit [CSB_WIDTH-1:0] active_csb = 0;

  virtual task reset_signals();
    forever begin
      @(negedge cfg.vif.rst_n);
      `uvm_info(`gfn, "\n  dev_drv: in reset progress", UVM_DEBUG)
      under_reset = 1'b1;
      cfg.vif.sio_out = 'z;
      @(posedge cfg.vif.rst_n);
      under_reset = 1'b0;
      `uvm_info(`gfn, "\n  dev_drv: out of reset", UVM_DEBUG)
    end
  endtask

  virtual task get_and_drive();
    spi_item req, rsp;

    forever begin
      seq_item_port.get_next_item(req);
      `DV_CHECK_EQ(cfg.vif.disconnected, 0)

      if (cfg.csb_sel_in_cfg) active_csb = cfg.csid;
      else                    active_csb = req.csb_sel;

      $cast(rsp, req.clone());
      rsp.set_id_info(req);
      // The response should read the payload actually consumed, not start with
      // it filled out.
      rsp.payload_q.delete();
      `uvm_info(`gfn, $sformatf("Received item - %s",req.sprint), UVM_DEBUG)
      wait (!under_reset && !cfg.vif.csb[active_csb]);
      fork
        begin: iso_fork
          fork
            case (cfg.spi_func_mode)
              SpiModeGeneric: send_rx_item(req, rsp);
              SpiModeFlash: send_flash_item(req, rsp);
              SpiModeTpm: send_tpm_item(req, rsp);
              default: begin
                `uvm_fatal(`gfn, $sformatf("Invalid mode %s", cfg.spi_func_mode.name))
              end
            endcase
            drive_bus_to_highz();
            drive_bus_for_reset();
          join_any
          disable fork;
        end: iso_fork
      join
      seq_item_port.item_done();
      seq_item_port.put_response(rsp);
      `uvm_info(`gfn, "\n  dev_drv: item done", UVM_HIGH)
    end
  endtask : get_and_drive

  virtual task send_rx_item(spi_item item, spi_item rsp);
    logic [3:0] sio_bits;
    bit         bits_q[$];
    int         max_tx_bits;

    if (cfg.byte_order) cfg.swap_byte_order(item.data);
    bits_q = {>> 1 {item.data}};
    max_tx_bits = cfg.get_sio_size();

    `uvm_info(`gfn, $sformatf("\n  dev_drv: send_rx_item, return %0d bits to dut",
                              bits_q.size()), UVM_DEBUG)
    // pop enough bits do drive all needed sio
    while (bits_q.size() > 0) begin
       if (bits_q.size() > 0) cfg.wait_sck_edge(DrivingEdge, active_csb);
      for (int i = 0; i < 4; i++) begin
        sio_bits[i] = (i < max_tx_bits) ? bits_q.pop_front() : 1'bz;
      end
      send_data_to_sio(cfg.spi_mode, sio_bits);
      `uvm_info(`gfn, $sformatf("\n  dev_drv: assert data bit[%0d] %b",
                                bits_q.size(), sio_bits[0]), UVM_DEBUG)

    end
    // TODO, ideally we should capture the data device receives and put in rsp.
  endtask : send_rx_item

  virtual task send_flash_item(spi_item item, spi_item rsp);
    logic [3:0] sio_bits;
    bit         bits_q[$];
    logic [7:0] data[$] = {item.payload_q};
    spi_mode_e spi_mode;

    `uvm_info(`gfn, $sformatf("sending rx_item:\n%s", item.sprint()), UVM_MEDIUM)

    fork
      begin : thread_collect_payload
        forever begin
          logic [7:0] byte_data;
          cfg.read_byte(item.num_lanes, !item.write_command, active_csb, byte_data);
          rsp.payload_q.push_back(byte_data);
          if (!item.write_command) rsp.read_size++;
        end
      end : thread_collect_payload

      begin : thread_send_read_data
        if (!item.write_command) begin
          if (cfg.byte_order) cfg.swap_byte_order(data);
          bits_q = {>> 1 {data}};

          if (item.num_lanes == 1) spi_mode = Standard;
          else if (item.num_lanes == 2) spi_mode = Dual;
          else spi_mode = Quad;

          forever begin
            cfg.wait_sck_edge(DrivingEdge, active_csb);
            // The first bit in bits_q is the MSB, which is driven on the sio
            // lane with the highest active index.
            for (int i = $high(sio_bits); i >= $low(sio_bits); i--) begin
              if (i >= item.num_lanes) begin
                sio_bits[i] = 1'bz;
              end else begin
                sio_bits[i] = bits_q.size > 0 ? bits_q.pop_front() : $urandom_range(0, 1);
              end
            end
            send_data_to_sio(spi_mode, sio_bits);
          end
        end
      end : thread_send_read_data
    join
  endtask : send_flash_item

  virtual task send_tpm_item(spi_item item, spi_item rsp);
    // TODO, this mode isn't used in OT project
    `uvm_fatal(`gfn, "TPM device mode isn't supported")
  endtask : send_tpm_item

  virtual task send_data_to_sio(spi_mode_e mode, input logic [3:0] sio_bits);
    `uvm_info(`gfn, $sformatf("%m: spi_mode = %p, sio_bits = 0x%0x", mode, sio_bits), UVM_DEBUG)
    case (mode)
      Standard: cfg.vif.sio_out[1]   <= sio_bits[0];
      Dual:     cfg.vif.sio_out[1:0] <= sio_bits[1:0];
      default:  cfg.vif.sio_out      <= sio_bits;
    endcase
  endtask : send_data_to_sio

  virtual task drive_bus_to_highz();
    @(posedge cfg.vif.csb[active_csb]);
    cfg.vif.sio_out = 'z;
    `uvm_info(`gfn, "\n  dev_drv: drive_bus_to_highz is done", UVM_DEBUG)
  endtask : drive_bus_to_highz

  virtual task drive_bus_for_reset();
    @(negedge cfg.vif.rst_n);
    cfg.vif.sio_out = 'z;
    `uvm_info(`gfn, "\n  dev_drv: drive_bus_for_reset is done", UVM_DEBUG)
  endtask : drive_bus_for_reset
endclass : spi_device_driver
