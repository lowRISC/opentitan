// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`ifndef __I2C_DRIVE_DRIVER__
`define __I2C_DRIVE_DRIVER__

class i2c_device_driver extends i2c_driver;
  `uvm_component_utils(i2c_device_driver)

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if ( cfg  == null )
      `uvm_fatal(`gtn, "failed due to null i2c_cfg")
  endfunction : build_phase

  virtual task run_phase(uvm_phase phase);
    // base class forks off reset_signals() and get_and_drive() tasks
    super.run_phase(phase);
    get_and_drive();
  endtask : run_phase

  // drive trans received from sequencer
  virtual task get_and_drive();
    bit      rd_bit;
    i2c_item item;

    item = i2c_item::type_id::create("item");
    if ( item  == null )
      `uvm_fatal(`gtn, "failed due to null item")

    forever begin
      seq_item_port.get_next_item(req);
      $cast(rsp, req.clone());
      rsp.set_id_info(req);
      `uvm_info(`gfn, $sformatf("rcvd item:\n%0s", req.sprint()), UVM_LOW)

      // do the driving part
      fork
        begin
          // randomize item

          item.randomize();
          // get r/w bit
          @(posedge cfg.vif.drv_cb.scl_i)
            cfg.i2c_rw_direction = cfg.vif.drv_cb.sda_i ? READ : WRITE;

          // get address bits
          for(int i = 0; i < `I2C_DEVICE_ADDR_WIDTH; i++) begin
            @(posedge cfg.vif.drv_cb.scl_i)
            cfg.device_addr[i] = cfg.vif.drv_cb.sda_i;
          end

          // send out ACK
          wait_for_ack_by_host();
          wait_for_rand_dly(item.dly_to_send_ack);
          send_ack_by_device();
        end

        begin
          // READ transaction
          if (cfg.i2c_rw_direction == READ) begin
            for (int i = 0; i < item.max_host_rd_byte; i++) begin
              `DV_CHECK_RANDOMIZE_FATAL(this)
              for (int j = 0; j < 8; j++) begin
                cfg.vif.drv_cb.scl_o <= 1'b0;
                wait_for_rand_dly(item.dly_to_send_rd_data);
                @(posedge cfg.vif.clk_i)
                cfg.vif.drv_cb.scl_o <= 1'b1;
                cfg.vif.drv_cb.sda_o <= rd_bit;
                req.data[i] = rd_bit;
              end
              if (i === item.max_host_rd_byte-1) begin // last rd data byte
                wait_for_rand_dly(item.dly_to_send_nack);
                wait_for_nack_by_host();
                wait_for_rand_dly(item.dly_to_send_stop);
                wait_for_stop_by_host();
                wait_for_rand_dly(item.dly_to_back_to_back);
              end else begin
                wait_for_rand_dly(item.dly_to_send_ack);
                wait_for_ack_by_host();
              end
            end
          end else begin
          // WRITE transaction
            for (int i = 0; i < item.max_host_wr_byte; i++) begin
              `DV_CHECK_RANDOMIZE_FATAL(this)
              for (int j = 0; j < 8; j++) begin
                @(posedge cfg.vif.clk_i)
                if (cfg.vif.drv_cb.scl_i === 1'b1) begin
                  rsp.data[i] = cfg.vif.drv_cb.sda_i;
                end
              end
              wait_for_rand_dly(item.dly_to_send_ack);
              send_ack_by_device();
              if (i === item.max_host_wr_byte) begin
                wait_for_rand_dly(item.dly_to_send_stop);
                wait_for_stop_by_host();
                wait_for_rand_dly(item.dly_to_back_to_back);
              end
            end
          end
        end
      join_any

      // send rsp back to seq
      `uvm_info(`gfn, "item sent", UVM_LOW)
      seq_item_port.item_done(rsp);
    end
  endtask : get_and_drive


endclass : i2c_device_driver

`endif // __I2C_DRIVE_DRIVER__