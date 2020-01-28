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
    super.reset_signals();
    fork
      get_and_drive();
    join
  endtask : run_phase

  // drive trans received from sequencer
  virtual task get_and_drive();
    bit [`I2C_DATA_WIDTH-1:0] data_byte;
    bit [`I2C_ADDR_WIDTH-1:0] addr_byte;
    bit                       nack = 1'b0;
    bit                       rw_dir = 1'b0;  // 1: READ, 0: WRITE

    forever begin
      if (cfg.is_active) begin
        seq_item_port.get_next_item(req);
        $cast(rsp, req.clone());
        rsp.set_id_info(req);
        `uvm_info(`gfn, $sformatf("i2c gets next item:\n%0s", req.sprint()), UVM_LOW)

        // do the driving part
        fork
          begin
            // randomize item
            void'(dev_item.randomize());

            // device waits for START on bus
            common_tasks.wait_for_start_by_host();

            // device gets R/W bit
            @(posedge cfg.vif.scl_i) begin
              addr_byte[0] = cfg.vif.sda_i;
              rw_dir = cfg.vif.sda_i;  // R/W bit
            end
            if (cfg.vif.sda_i)
              `uvm_info(`gtn, "i2c host reads from target", UVM_LOW)
            else
              `uvm_info(`gtn, "i2c host writes to target", UVM_LOW)

            // device gets ADDRESS bits
            for(int i = 1; i < `I2C_ADDR_WIDTH; i++) begin
              @(posedge cfg.vif.scl_i);
              addr_byte[i] = cfg.vif.sda_i;
            end
            req.addr = addr_byte;
            // if loopback test, push back address into queue
            if (cfg.en_loopback)
              dev_item.mem_addrs.push_back(addr_byte);

            // device sends ACK to host
            common_tasks.wait_for_rand_dly(cfg.dly_to_send_ack);
            common_tasks.send_ack_by_device();
          end

          begin
            `DV_CHECK_RANDOMIZE_FATAL(this)

            // READ transaction
            if (rw_dir === 1'b1  && cfg.en_tx_monitor === 1'b1) begin
              data_byte = (cfg.en_loopback) ? dev_item.mem_datas.pop_front() : dev_item.rd_data;
              if (cfg.en_loopback && dev_item.mem_addrs.pop_front() !== addr_byte)
                `uvm_error(`gtn, "i2c loopback reads an incorrect address")

              for (int i = 0; i < `I2C_DATA_WIDTH; i++) begin
                cfg.vif.scl_o <= 1'b0;
                common_tasks.wait_for_rand_dly(cfg.dly_to_send_rd_data);
                @(posedge cfg.vif.clk_i);
                cfg.vif.scl_o <= 1'b1;
                cfg.vif.sda_o <= data_byte[i];
              end
              req.num_host_rd_byte++;
              req.rd_data = data_byte;

              fork
                common_tasks.wait_for_ack_by_host();
                common_tasks.wait_for_nack_by_host(.nack(nack));
              join_any
              // wait for STOP if NACK detected
              while (nack) common_tasks.wait_for_stop_by_host();
            end

            // WRITE transaction
            if (rw_dir === 1'b0 && cfg.en_rx_monitor === 1'b1) begin
              for (int i = 0; i < `I2C_DATA_WIDTH; i++) begin
                @(posedge cfg.vif.clk_i)
                if (cfg.vif.scl_i === 1'b1) begin
                  data_byte[i] = cfg.vif.sda_i;
                end
              end
              req.num_host_wr_byte++;
              rsp.wr_data = data_byte;
              // if loopback test, push back data into queue
              if (cfg.en_loopback)
                dev_item.mem_datas.push_back(data_byte);

              common_tasks.wait_for_rand_dly(cfg.dly_to_send_ack);
              common_tasks.send_ack_by_device();
              fork
                common_tasks.wait_for_stop_by_host();
                common_tasks.wait_for_repstart_by_host();
              join_any
            end
          end
        join_any

        // send rsp back to seq
        `uvm_info(`gfn, "device item sent", UVM_LOW)
        seq_item_port.item_done(rsp);
      end else begin
        // i2c slave pulls up pins, idle bus
        cfg.vif.scl_o <= 1'b1;
        cfg.vif.sda_o <= 1'b1;
      end
    end
  endtask : get_and_drive


endclass : i2c_device_driver

`endif // __I2C_DRIVE_DRIVER__