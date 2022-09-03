// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_driver extends dv_base_driver #(i2c_item, i2c_agent_cfg);
  `uvm_component_utils(i2c_driver)

  `uvm_component_new

  rand bit [7:0] rd_data[256]; // max length of read transaction
  byte wr_data;

  // loopback storage queue - the 256 represent different i2c devices.
  // The loopback option takes every write to a specific device and shoves
  // it into a queue.  When a read is later performed on that device, the
  // same data is returned in the same order it was received.
  uvm_tlm_analysis_fifo #(i2c_item) lb_fifo[256];

  // get an array with unique read data
  constraint rd_data_c { unique { rd_data }; }

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    foreach (lb_fifo[i])
      lb_fifo[i] = new($sformatf("lb_fifo[%0d]", i), this);
  endfunction

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
     unique case (req.drv_type)
      HostStart: begin
        cfg.vif.host_start(cfg.timing_cfg);
      end
      HostRStart: begin
        cfg.vif.host_rstart(cfg.timing_cfg);
      end
      HostData: begin
        for (int i = $bits(wr_data) -1; i >= 0; i--) begin
          cfg.vif.host_data(cfg.timing_cfg, wr_data[i]);
        end
      end
      HostNAck: begin
        cfg.vif.host_nack(cfg.timing_cfg);
      end
      HostStop: begin
        cfg.vif.host_stop(cfg.timing_cfg);
      end
      default: begin
        `uvm_fatal(`gfn, $sformatf("\n  host_driver, received invalid request"))
      end
    endcase
  endtask : drive_host_item

  virtual task drive_device_item(i2c_item req);
    bit [7:0] rd_data_cnt = 8'd0;
    bit [7:0] rdata;
    bit [9:0] address = req.addr;

    unique case (req.drv_type)
      DevAck: begin
        cfg.timing_cfg.tStretchHostClock = gen_num_stretch_host_clks(cfg.timing_cfg);
         `uvm_info(`gfn, $sformatf("sending an ack"), UVM_MEDIUM)
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
        if (cfg.en_loopback) begin
          i2c_item item;
          `uvm_info(`gfn, $sformatf("Loopback read address %0x", address), UVM_MEDIUM)
          lb_fifo[address].try_get(item);
          if (item == null) begin
            `uvm_fatal(`gfn, $sformatf("Loopback requested on empty queue"))
          end else begin
            rdata = item.lb_data;
          end
        end else begin
          if (rd_data_cnt == 8'd0) begin
             `DV_CHECK_MEMBER_RANDOMIZE_FATAL(rd_data)
          end
          rdata = rd_data[rd_data_cnt];
        end

        `uvm_info(`gfn, $sformatf("Send readback data %0x", rdata), UVM_MEDIUM)
        for (int i = 7; i >= 0; i--) begin
          cfg.vif.device_send_bit(cfg.timing_cfg, rdata[i]);
        end
        `uvm_info(`gfn, $sformatf("\n  device_driver, trans %0d, byte %0d  %0x",
            req.tran_id, req.num_data+1, rd_data[rd_data_cnt]), UVM_DEBUG)
        // rd_data_cnt is rollled back (no overflow) after reading 256 bytes
        rd_data_cnt++;
      end
      WrData: begin
        // nothing to do here at the moment
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
    i2c_item dummy;
    @(negedge cfg.vif.rst_ni);
    release_bus();
    // on reset just wipe out the entire storage
    foreach (lb_fifo[i]) begin
      while (lb_fifo[i].used() > 0) lb_fifo[i].get(dummy);
    end
    `uvm_info(`gfn, "\n  driver is reset", UVM_DEBUG)
  endtask : process_reset

  virtual task release_bus();
    `uvm_info(`gfn, "Driver released the bus", UVM_MEDIUM)
    cfg.vif.scl_o = 1'b1;
    cfg.vif.sda_o = 1'b1;
  endtask : release_bus



endclass : i2c_driver
