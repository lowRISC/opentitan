// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_device_driver extends i2c_driver;
  `uvm_component_utils(i2c_device_driver)
  `uvm_component_new

  bit [I2C_DATA_WIDTH-1:0] data;

  rand bit [I2C_DATA_WIDTH-1:0] rd_data;

  constraint rd_data_c { rd_data inside {[0 : ((1 << I2C_DATA_WIDTH) - 1)]}; }

  virtual task get_and_drive();
    i2c_item rsp_item;
    @(posedge cfg.vif.rst_ni);
    forever begin
      cfg.vif.scl_o = 1'b1;
      cfg.vif.sda_o = 1'b1;
      // device driver responses to dut
      seq_item_port.get_next_item(rsp_item);
      unique case (rsp_item.drv_type)
        DevAck: begin
          cfg.vif.device_send_ack(cfg.timing_cfg);
        end
        RdData: begin
          `DV_CHECK_MEMBER_RANDOMIZE_FATAL(rd_data)
          for (int i = I2C_DATA_WIDTH-1; i >= 0; i--) begin
            cfg.vif.device_send_bit(cfg.timing_cfg, rd_data[i]);
          end
          `uvm_info(`gfn, $sformatf("driver, trans %0d, byte %0d  %0b",
              rsp_item.tran_id, rsp_item.num_data+1, rd_data), UVM_DEBUG)
        end
        default: begin
          `uvm_fatal(`gfn, $sformatf("driver, received invalid request from monitor/seq"))
        end
      endcase
      seq_item_port.item_done();
    end
  endtask : get_and_drive

endclass : i2c_device_driver

