// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_driver extends dv_base_driver #(i2c_item, i2c_agent_cfg);
  `uvm_component_utils(i2c_driver)

  `uvm_component_new

  rand bit [7:0] rd_data[256]; // max length of read transaction
  byte wr_data;
  int scl_spinwait_timeout_ns = 1_000_000; // 1ms
  bit scl_pause = 0;

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

  virtual task run_phase(uvm_phase phase);
    fork
      reset_signals();
      get_and_drive();
      begin
        if (cfg.if_mode == Host) drive_scl();
      end
      begin
        if (cfg.if_mode == Host) host_scl_pause_ctrl();
      end
    join_none
  endtask

  virtual task get_and_drive();
    i2c_item req;
    @(posedge cfg.vif.rst_ni);
    forever begin
      if (cfg.if_mode == Device) release_bus();
      // driver drives bus per mode
      seq_item_port.get_next_item(req);
      fork
        begin: iso_fork
          fork
            begin
              case (cfg.if_mode)
                Host: drive_host_item(req);
                Device: drive_device_item(req);
                default: `uvm_fatal(`gfn, "Shouldn't reach this state!")
              endcase
            end
            // handle on-the-fly reset
            begin
              process_reset();
              req.clear_all();
            end
            begin
              // Agent hot reset. It only resets I2C agent.
              // The DUT functions normally without reset.
              // This event only happens in directed test case so cannot set the timeout.
              // It will be killed by disable fork when 'drive_*_item' is finished.
              wait(cfg.driver_rst);
              `uvm_info(`gfn, "drvdbg agent reset", UVM_MEDIUM)
              req.clear_all();
            end
          join_any
          disable fork;
        end: iso_fork
      join
      seq_item_port.item_done();
      // When agent reset happens, flush all sequence items from sequencer request queue,
      // before it starts a new sequence.
      if (cfg.driver_rst) begin
        i2c_item dummy;
        do begin
          seq_item_port.try_next_item(dummy);
          if (dummy != null) seq_item_port.item_done();
        end while (dummy != null);
      end
    end
  endtask : get_and_drive

  // Task to drive bits on SDA from TB to DUT while DUT is operating in Target mode
  virtual task drive_host_data_bits(ref i2c_item req);
    int num_bits = $bits(req.wdata);
    `uvm_info(`gfn, $sformatf("Driving host item 8'h%2x", req.wdata), UVM_FULL)
    `uvm_info(`gfn, $sformatf("wait_cycles = %0d", req.wait_cycles), UVM_DEBUG)
    for (int i = num_bits - 1; i >= (num_bits - req.wait_cycles); i--) begin
      cfg.vif.host_data(cfg.timing_cfg, req.wdata[i]);
    end
  endtask

  virtual task drive_host_item(i2c_item req);
    // During pause period, let drive_scl control scl
    `DV_WAIT(scl_pause == 1'b0,, scl_spinwait_timeout_ns, "drive_host_item")

    // Print out what we are about to drive...
    begin
      string str = $sformatf("drive_host_item() :: drv_type=%s", req.drv_type.name());
      case (req.drv_type)
        HostData: str = {str, $sformatf(" ( byte=8'h%2x )", req.wdata)};
        HostDataNoWaitForACK: begin
          str = {str, $sformatf(" ( byte=8'h%2x, wait_cycles=%0d )", req.wdata, req.wait_cycles)};
        end
        default:; // Fall-through
      endcase
      `uvm_info(`gfn, str, UVM_HIGH)
    end

    // Now drive the item.
    case (req.drv_type)
      HostStart: begin
        cfg.vif.host_start(cfg.timing_cfg);
        cfg.host_scl_start = 1;
      end
      HostRStart: begin
        cfg.vif.host_rstart(cfg.timing_cfg);
      end
      HostData: begin
        drive_host_data_bits(req);
        cfg.vif.wait_scl(.iter(1), .tc(cfg.timing_cfg));
      end
      HostDataNoWaitForACK: begin
        drive_host_data_bits(req);
      end
      HostAck: begin // Wait for 8-bits of data, then drive an ACK
        cfg.vif.wait_scl(.iter(8), .tc(cfg.timing_cfg));
        cfg.vif.host_data(cfg.timing_cfg, 0);
      end
      HostNAck: begin // Wait for 8-bits of data, then drive a NACK
        cfg.vif.wait_scl(.iter(8), .tc(cfg.timing_cfg));
        cfg.vif.host_data(cfg.timing_cfg, 1);
      end
      HostWait: begin
        // Wait for wait_cycles number of SCL cycles
        `uvm_info(`gfn, $sformatf("wait_cycles = %0d", req.wait_cycles), UVM_DEBUG)
        for (int i = 0; i < req.wait_cycles; i++) begin
          cfg.vif.wait_scl(.iter(1), .tc(cfg.timing_cfg));
        end
      end
      HostStop: begin
        // If SCL is paused high, wait for it to fall.
        `DV_WAIT(cfg.vif.scl_i === 1'b0,, scl_spinwait_timeout_ns, "drive_host_item HostStop")
        // Now disable the SCL drive thread.
        cfg.host_scl_stop = 1;
        cfg.vif.host_stop(cfg.timing_cfg);
      end
      default: begin
        `uvm_fatal(`gfn, {"drive_host_item() received invalid drv_type : ", req.drv_type.name()})
      end
    endcase
  endtask : drive_host_item

  virtual task drive_device_item(i2c_item req);
    bit [7:0] rd_data_cnt = 8'd0;
    bit [7:0] rdata;

    `uvm_info(`gfn, $sformatf("drive_device_item() :: drv_type=%s", req.drv_type.name), UVM_HIGH)

    // Choose a randomized stretching delay for this item.
    // - If cfg.host_stretch_test_mode == 1, this delay is not randomized.
    cfg.timing_cfg.tStretchHostClock = gen_num_stretch_host_clks(cfg.timing_cfg);

    case (req.drv_type)
      DevAck: begin
        `uvm_info(`gfn, $sformatf("DevAck : sending an ACK (after stretching for %0d cycles)",
                                  cfg.timing_cfg.tStretchHostClock), UVM_FULL)
        fork
          // host clock stretching allows a high-speed host to communicate
          // with a low-speed device by setting TIMEOUT_CTRL.EN bit
          // the device asks host stretching its scl_i by pulling down scl_o
          // the host clock pulse is extended until device scl_o is pulled up
          // once scl_o is pulled down longer than TIMEOUT_CTRL.VAL field,
          // intr_stretch_timeout_o is asserted (ref. https://www.i2c-bus.org/clock-stretching)
          cfg.vif.device_stretch_host_clk(cfg.timing_cfg);
          cfg.vif.device_send_ack(cfg.timing_cfg, .can_stretch(1'b1));
        join
      end
      DevNack: begin
        cfg.vif.device_send_nack(cfg.timing_cfg);
      end
      RdData: begin
        `uvm_info(`gfn, $sformatf("RdData : Driving read data 8'h%2x", req.rdata), UVM_FULL)
        for (int i = 7; i >= 0; i--) begin
          cfg.vif.device_send_bit(cfg.timing_cfg, req.rdata[i], .can_stretch(1'b0));
        end
        // rd_data_cnt is rollled back (no overflow) after reading 256 bytes
        rd_data_cnt++;
      end
      default: begin
        `uvm_fatal(`gfn, {"drive_device_item() received invalid drv_type : ", req.drv_type.name()})
      end
    endcase
  endtask : drive_device_item

  function int gen_num_stretch_host_clks(ref timing_cfg_t tc);
    // By randomly pulling down scl_o "offset" within [0:2*tc.tTimeOut],
    // intr_stretch_timeout_o interrupt would be generated uniformly
    // To test this feature more regressive, there might need a dedicated vseq (V2)
    // in which TIMEOUT_CTRL.EN is always set.

    // If Stretch value is greater than 2*tTimeOut, it will create 2 interrupt events.
    // Which can cause false error in 'host_stretch_testmode'.
    // So, this value should be associated with tTimeout in host stretch testmode
    int random_stretch = $urandom_range(tc.tClockPulse,
                                        tc.tClockPulse + 2*tc.tTimeOut);

    return (cfg.host_stretch_test_mode) ? (tc.tTimeOut + 1) :
                                          random_stretch;
  endfunction : gen_num_stretch_host_clks

  virtual task process_reset();
    @(negedge cfg.vif.rst_ni);
    release_bus();
    `uvm_info(`gfn, "\n  driver is reset", UVM_DEBUG)
  endtask : process_reset

  virtual task release_bus();
    `uvm_info(`gfn, "Driver released the bus", UVM_DEBUG)
    cfg.vif.scl_o = 1'b1;
    cfg.vif.sda_o = 1'b1;
  endtask : release_bus

  task drive_scl();
    // This timeout is extremely long since read transactions will stretch
    // whenever there are unhanded write commands or format bytes.
    int scl_spinwait_timeout_ns = 100_000_000; // 100ms
    forever begin
      @(cfg.vif.cb);
      wait(cfg.host_scl_start);
      fork begin
        fork
          // Original scl driver thread
          while(!cfg.host_scl_stop) begin
            cfg.vif.scl_o <= 1'b0;
            cfg.vif.wait_for_dly(cfg.timing_cfg.tClockLow);
            cfg.vif.wait_for_dly(cfg.timing_cfg.tSetupBit);
            if (cfg.host_scl_stop) break;
            cfg.vif.scl_o <= 1'b1;
            `DV_WAIT(cfg.vif.scl_i === 1'b1,, scl_spinwait_timeout_ns, "i2c_drv_scl")
            cfg.vif.wait_for_dly(cfg.timing_cfg.tClockPulse);

            // There is a corner case s.t.
            // pause req -> drv got stop back to back.
            // if that happens, skip to the next txn cycle to pause
            // to avoid unsuccessful host timeout
            if (cfg.host_scl_pause_ack & !cfg.host_scl_stop) begin
              scl_pause = 1;
              cfg.vif.wait_for_dly(cfg.host_scl_pause_cyc);
              scl_pause = 0;
              cfg.host_scl_pause_ack = 0;
            end
            if (!cfg.host_scl_stop) cfg.vif.scl_o = 1'b0;
            cfg.vif.wait_for_dly(cfg.timing_cfg.tHoldBit);
          end
          // Force quit thread
          begin
            wait(cfg.host_scl_force_high | cfg.host_scl_force_low);
            cfg.host_scl_stop = 1;
            if (cfg.host_scl_force_high) begin
              cfg.vif.scl_o <= 1'b1;
              cfg.vif.sda_o <= 1'b1;
            end else begin
              cfg.vif.scl_o <= 1'b0;
              cfg.vif.sda_o <= 1'b0;
            end
          end
        join_any
        disable fork;
      end join
      cfg.host_scl_start = 0;
      cfg.host_scl_stop = 0;
    end
  endtask

  task host_scl_pause_ctrl();
     forever begin
        @(cfg.vif.cb);
        if (cfg.host_scl_pause_req & cfg.host_scl_start & !cfg.host_scl_stop) begin
          cfg.host_scl_pause_ack = 1;
          `DV_WAIT(cfg.host_scl_pause_ack == 0,,
                   scl_spinwait_timeout_ns, "host_scl_pause_ctrl")
          cfg.host_scl_pause_req = 0;
        end
     end
  endtask

endclass : i2c_driver
