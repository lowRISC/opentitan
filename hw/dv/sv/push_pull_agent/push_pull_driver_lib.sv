// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

typedef class push_pull_sub_driver;
typedef class push_host_driver;
typedef class pull_host_driver;
typedef class push_device_driver;
typedef class pull_device_driver;

// 'Main' driver class that is created by the agent in active mode.
//
// The actual driving of signals is done by the 'sub' driver class which is virtualized. The correct
// flavor of the sub driver is picked up base on whether it is a push / pull and whether its host or
// device.
class push_pull_driver #(
    parameter int HostDataWidth   = 32,
    parameter int DeviceDataWidth = HostDataWidth
) extends dv_base_driver #(
    .ITEM_T(push_pull_item #(HostDataWidth, DeviceDataWidth)),
    .CFG_T (push_pull_agent_cfg #(HostDataWidth, DeviceDataWidth))
);

  push_pull_sub_driver #(HostDataWidth, DeviceDataWidth) sub_driver;

  `uvm_component_param_utils(push_pull_driver#(HostDataWidth, DeviceDataWidth))
  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    case ({cfg.if_mode, cfg.agent_type})
      {dv_utils_pkg::Host, PushAgent}: begin
        sub_driver = push_host_driver#(HostDataWidth, DeviceDataWidth)::type_id::create(
            "sub_driver");
      end
      {dv_utils_pkg::Host, PullAgent}: begin
        sub_driver = pull_host_driver#(HostDataWidth, DeviceDataWidth)::type_id::create(
            "sub_driver");
      end
      {dv_utils_pkg::Device, PushAgent}: begin
        sub_driver = push_device_driver#(HostDataWidth, DeviceDataWidth)::type_id::create(
            "sub_driver");
      end
      {dv_utils_pkg::Device, PullAgent}: begin
        sub_driver = pull_device_driver#(HostDataWidth, DeviceDataWidth)::type_id::create(
            "sub_driver");
      end
      default:;
    endcase
    sub_driver.cfg = cfg;
  endfunction

  virtual task reset_signals();
    sub_driver.reset_signals();
    forever begin
      @(negedge cfg.vif.rst_n);
      `uvm_info(`gfn, "Driver is under reset", UVM_HIGH)
      sub_driver.reset_signals();
      @(posedge cfg.vif.rst_n);
      `uvm_info(`gfn, "Driver is out of reset", UVM_HIGH)
    end
  endtask

  // Drive trans received from sequencer.
  virtual task get_and_drive();
    forever begin
      seq_item_port.try_next_item(req);
      if (req == null) begin
        sub_driver.wait_cb();
        continue;
      end

      `uvm_info(`gfn, $sformatf("Driver received item:\n%0s", req.convert2string()), UVM_HIGH)
      sub_driver.drive_item(req);
      seq_item_port.item_done(req);
    end
  endtask

endclass

// Virtual 'sub' driver class.
//
// Extended to provide different push / pull / host / device mode flavors.
virtual class push_pull_sub_driver #(
    parameter int HostDataWidth   = 32,
    parameter int DeviceDataWidth = HostDataWidth
) extends uvm_object;

  // The handle to the agent cfg object set by the main driver.
  push_pull_agent_cfg #(HostDataWidth, DeviceDataWidth) cfg;

  `uvm_object_new

  // Reset the interface signals driven to the DUT.
  pure virtual function void reset_signals();

  // Wait for clock edges using the appropriate clocking block.
  pure virtual task wait_cb(int num = 1);

  // Apply the item to the interface.
  pure virtual task drive_item(push_pull_item#(HostDataWidth, DeviceDataWidth) req);

endclass

// Push driver in host mode.
class push_host_driver #(
    parameter int HostDataWidth   = 32,
    parameter int DeviceDataWidth = HostDataWidth
) extends push_pull_sub_driver #(HostDataWidth, DeviceDataWidth);

  `uvm_object_param_utils(push_host_driver#(HostDataWidth, DeviceDataWidth))
  `uvm_object_new

  `define CB cfg.vif.host_push_cb

  virtual function void reset_signals();
    cfg.vif.valid_int <= '0;
    cfg.vif.h_data_int <= 'x;
  endfunction

  virtual task wait_cb(int num = 1);
    repeat (num) @(`CB);
  endtask

  // Drives host side of ready/valid protocol
  virtual task drive_item(push_pull_item#(HostDataWidth, DeviceDataWidth) req);
    `DV_SPINWAIT_EXIT(
        repeat (req.host_delay) @(`CB);
        `CB.valid_int <= 1'b1;
        `CB.h_data_int <= req.h_data;
        do @(`CB); while (!cfg.ignore_push_host_backpressure && !`CB.ready);
        `CB.valid_int <= 1'b0;
        if (!cfg.hold_h_data_until_next_req) `CB.h_data_int <= 'x;,
        wait (cfg.in_reset);)
    // In case there is race condition between the logic above and reset_signals task.
    // We always set the valid_int again to 0 to make sure the data comes out of reset is not
    // valid.
    if (cfg.in_reset) `CB.valid_int <= '0;
  endtask

  `undef CB

endclass

// Pull driver in host mode.
class pull_host_driver #(
    parameter int HostDataWidth   = 32,
    parameter int DeviceDataWidth = HostDataWidth
) extends push_pull_sub_driver #(HostDataWidth, DeviceDataWidth);

  `uvm_object_param_utils(pull_host_driver#(HostDataWidth, DeviceDataWidth))
  `uvm_object_new

  `define CB cfg.vif.host_pull_cb

  virtual function void reset_signals();
    cfg.vif.req_int <= '0;
    cfg.vif.h_data_int <= 'x;
  endfunction

  virtual task wait_cb(int num = 1);
    repeat (num) @(`CB);
  endtask

  // Drives host side of req/ack protocol
  virtual task drive_item(push_pull_item#(HostDataWidth, DeviceDataWidth) req);
    `DV_SPINWAIT_EXIT(
        repeat (req.host_delay) @(`CB);
        `CB.req_int <= 1'b1;
        `CB.h_data_int <= req.h_data;
        do @(`CB); while (!`CB.ack);
        if (cfg.pull_handshake_type == FourPhase) begin
          repeat (req.req_lo_delay) @(`CB);
          `CB.req_int <= 1'b0;
          do @(`CB); while (`CB.ack);
        end else begin
          `CB.req_int <= 1'b0;
        end
        if (!cfg.hold_h_data_until_next_req) `CB.h_data_int <= 'x;,
        wait (cfg.in_reset);)
  endtask

  `undef CB

endclass

// Push driver in device mode.
class push_device_driver #(
    parameter int HostDataWidth   = 32,
    parameter int DeviceDataWidth = HostDataWidth
) extends push_pull_sub_driver #(HostDataWidth, DeviceDataWidth);

  `uvm_object_param_utils(push_device_driver#(HostDataWidth, DeviceDataWidth))
  `uvm_object_new

  `define CB cfg.vif.device_push_cb

  virtual function void reset_signals();
    cfg.vif.ready_int <= '0;
    cfg.vif.d_data_int <= 'x;
  endfunction

  virtual task wait_cb(int num = 1);
    repeat (num) @(`CB);
  endtask

  // Drives device side of ready/valid protocol
  virtual task drive_item(push_pull_item#(HostDataWidth, DeviceDataWidth) req);
    `DV_SPINWAIT_EXIT(
        // TODO: this may be needed in future: while (!`CB.valid) @(`CB);
        repeat (req.device_delay) @(`CB);
        `CB.ready_int <= 1'b1;
        `CB.d_data_int <= req.d_data;
        @(`CB);
        `CB.ready_int <= 1'b0;
        if (!cfg.hold_d_data_until_next_req) `CB.d_data_int <= 'x;,
        wait (cfg.in_reset);)
  endtask

  `undef CB

endclass

// Pull driver in device mode.
class pull_device_driver #(
    parameter int HostDataWidth   = 32,
    parameter int DeviceDataWidth = HostDataWidth
) extends push_pull_sub_driver #(HostDataWidth, DeviceDataWidth);

  `uvm_object_param_utils(pull_device_driver#(HostDataWidth, DeviceDataWidth))
  `uvm_object_new

  `define CB cfg.vif.device_pull_cb

  virtual function void reset_signals();
    cfg.vif.ack_int <= '0;
    cfg.vif.d_data_int <= 'x;
  endfunction

  virtual task wait_cb(int num = 1);
    repeat (num) @(`CB);
  endtask

  // Drives device side of req/ack protocol
  virtual task drive_item(push_pull_item#(HostDataWidth, DeviceDataWidth) req);
    `DV_SPINWAIT_EXIT(
        while (!`CB.req) @(`CB);
        repeat (req.device_delay) @(`CB);
        `CB.ack_int <= 1'b1;
        `CB.d_data_int <= req.d_data;
        if (cfg.pull_handshake_type == FourPhase) begin
          do @(`CB); while (`CB.req);
          repeat (req.ack_lo_delay) @(`CB);
        end else begin
          @(`CB);
        end
        `CB.ack_int <= 1'b0;
        if (!cfg.hold_d_data_until_next_req) `CB.d_data_int <= 'x;,
        wait (cfg.in_reset);)
  endtask

  `undef CB

endclass
