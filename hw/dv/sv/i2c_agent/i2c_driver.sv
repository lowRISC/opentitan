// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_driver extends dv_base_driver #(i2c_item, i2c_agent_cfg);
  `uvm_component_utils(i2c_driver)

  `uvm_component_new

  rand bit [7:0] rd_data[256]; // max length of read transaction
  bit [7:0] wr_data;
  bit [7:0] address;
  // get an array with unique read data
  constraint rd_data_c { unique { rd_data }; }

  virtual task reset_signals();
    forever begin
      @(negedge cfg.vif.rst_ni);
      `uvm_info(`gfn, "\ndriver in reset progress", UVM_DEBUG)
      release_bus();
      @(posedge cfg.vif.rst_ni);
      `uvm_info(`gfn, "\ndriver out of reset", UVM_DEBUG)
    end
  endtask : reset_signals

  virtual task get_and_drive();
    i2c_item req;

    @(posedge cfg.vif.rst_ni);
    forever begin
      release_bus();
      // driver drives bus per mode
      seq_item_port.get_next_item(req);
      fork
        begin: iso_fork
          fork
            begin
              if (cfg.if_mode == Device) drive_device_item(req);
              else                       drive_host_item(req);
            end
            // handle on-the-fly reset
            begin
              process_reset();
              req.clear_all();
            end
          join_any
          disable fork;
        end: iso_fork
      join
      seq_item_port.item_done();
    end
  endtask : get_and_drive

  // TODO: drive_host_item is WiP
  virtual task drive_host_item(i2c_item req);
    // TODO
  endtask : drive_host_item

  virtual task drive_device_item(i2c_item req);
    bit [7:0] rd_data_cnt = 8'd0;

    unique case (req.drv_type)
      DevAck: begin
        cfg.timing_cfg.tStretchHostClock = gen_num_stretch_host_clks(cfg.timing_cfg);
        fork
          // host clock stretching allows a high-speed host to communicate
          // with a low-speed device by setting TIMEOUT_CTRL.EN bit
          // the device asks host stretching its scl_i by pulling down scl_o
          // the host clock pulse is extended until device scl_o is pulled up
          // once scl_o is pulled down longer than TIMEOUT_CTRL.VAL field,
          // intr_stretch_timeout_o is asserted (ref. https://www.i2c-bus.org/clock-stretching)
          cfg.vif.device_stretch_host_clk(cfg.timing_cfg);
          cfg.vif.device_send_ack(cfg.timing_cfg);
        join
      end
      RdData: begin
        if (rd_data_cnt == 8'd0) `DV_CHECK_MEMBER_RANDOMIZE_FATAL(rd_data)
        for (int i = 7; i >= 0; i--) begin
          cfg.vif.device_send_bit(cfg.timing_cfg, rd_data[rd_data_cnt][i]);
        end
        `uvm_info(`gfn, $sformatf("\n  device_driver, trans %0d, byte %0d  %0x",
            req.tran_id, req.num_data+1, rd_data[rd_data_cnt]), UVM_DEBUG)
        // rd_data_cnt is rollled back (no overflow) after reading 256 bytes
        rd_data_cnt++;
      end
      WrData:
        // TODO: consider adding memory (associative array) in device_driver
        for (int i = 7; i >= 0; i--) begin
          cfg.vif.get_bit_data("host", cfg.timing_cfg, wr_data[i]);
        end
      default: begin
        `uvm_fatal(`gfn, $sformatf("\n  device_driver, received invalid request"))
      end
    endcase
  endtask : drive_device_item

  function int gen_num_stretch_host_clks(ref timing_cfg_t tc);
    // By randomly pulling down scl_o "offset" within [0:2*tc.tTimeOut],
    // intr_stretch_timeout_o interrupt would be generated uniformly
    // To test this feature more regressive, there might need a dedicated vseq (V2)
    // in which TIMEOUT_CTRL.EN is always set.
    return $urandom_range(tc.tClockPulse, tc.tClockPulse + 2*tc.tTimeOut);
  endfunction : gen_num_stretch_host_clks

  virtual task process_reset();
    @(negedge cfg.vif.rst_ni);
    release_bus();
    `uvm_info(`gfn, "\n  driver is reset", UVM_DEBUG)
  endtask : process_reset
  
  virtual task release_bus();
    cfg.vif.scl_o = 1'b1;
    cfg.vif.sda_o = 1'b1;
  endtask : release_bus

endclass : i2c_driver
