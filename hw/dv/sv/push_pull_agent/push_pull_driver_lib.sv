// Copyright lowRISC contributors.
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
    // initial reset at start of test
    sub_driver.reset_signals();
    forever begin
      @(negedge cfg.vif.rst_n);
      `uvm_info(`gfn, "Driver is resetting", UVM_HIGH)
      sub_driver.set_in_reset(1'b1);
      sub_driver.reset_signals();
      @(posedge cfg.vif.rst_n);
      `uvm_info(`gfn, "Driver is out of reset", UVM_HIGH)
      sub_driver.set_in_reset(1'b0);
    end
  endtask

  // Drive trans received from sequencer.
  virtual task get_and_drive();
    // Wait for the initial reset to pass.
    @(posedge cfg.vif.rst_n);

    forever begin
      seq_item_port.try_next_item(req);
      if (req == null) begin
        sub_driver.wait_cb();
        continue;
      end

      `uvm_info(`gfn, $sformatf("Driver received item:\n%0s", req.convert2string()), UVM_HIGH)
      if (sub_driver.get_in_reset()) begin
        `uvm_info(`gfn, "Item not applied to the DUT due to reset assertion", UVM_HIGH)
      end else begin
        sub_driver.drive_item(req);
      end
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

  // Indicates that the interface is in reset.
  protected bit in_reset;

  // The handle to the agent cfg object set by the main driver.
  push_pull_agent_cfg #(HostDataWidth, DeviceDataWidth) cfg;

  `uvm_object_new

  // Tell if the interface is in or out of reset.
  //
  // The main driver already implements a task that monitors the interface reset. The sub driver's
  // in_reset bit is controlled by the main driver through this function.
  virtual function void set_in_reset(bit in_reset);
    this.in_reset = in_reset;
  endfunction

  // Returns the in_reset value.
  virtual function bit get_in_reset();
    return in_reset;
  endfunction

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
        `CB.valid_int  <= 1'b1;
        `CB.h_data_int <= req.h_data;
        do begin
          @(`CB);
        end while (!`CB.ready);
        `CB.valid_int <= 1'b0;
        if (!cfg.hold_h_data_until_next_req) `CB.h_data_int <= 'x;,
        wait(in_reset);)
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
        `CB.req_int    <= 1'b1;
        `CB.h_data_int <= req.h_data;
        do begin
          @(`CB);
        end while (!`CB.ack);
        `CB.req_int <= 1'b0;
        if (!cfg.hold_h_data_until_next_req) `CB.h_data_int <= 'x;,
        wait(in_reset);)
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
        repeat (req.device_delay) @(`CB);
        `CB.ready_int  <= 1'b1;
        `CB.d_data_int <= req.d_data;
        @(`CB);
        `CB.ready_int  <= 1'b0;
        if (!cfg.hold_d_data_until_next_req) `CB.d_data_int <= 'x;,
        wait(in_reset);)
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
        `CB.ack_int    <= 1'b1;
        `CB.d_data_int <= req.d_data;
        @(`CB);
        `CB.ack_int    <= 1'b0;
        if (!cfg.hold_d_data_until_next_req) `CB.d_data_int <= 'x;,
        wait(in_reset);)
  endtask

  `undef CB

endclass
