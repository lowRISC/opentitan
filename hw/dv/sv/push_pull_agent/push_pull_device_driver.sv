// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`define PUSH_DRIVER cfg.vif.device_push_cb
`define PULL_DRIVER cfg.vif.device_pull_cb

class push_pull_device_driver #(parameter int HostDataWidth = 32,
                                parameter int DeviceDataWidth = HostDataWidth)
  extends push_pull_driver #(HostDataWidth, DeviceDataWidth);

  `uvm_component_param_utils(push_pull_device_driver#(HostDataWidth, DeviceDataWidth))

  // the base class provides the following handles for use:
  // push_pull_agent_cfg: cfg

  `uvm_component_new

  virtual task do_reset();
    if (cfg.agent_type == PushAgent) begin
      cfg.vif.ready_int <= '0;
    end else begin
      cfg.vif.ack_int   <= '0;
    end
    cfg.vif.d_data_int <= 'x;
  endtask

  virtual task get_and_drive();
    forever begin
      // wait for reset to be completed and avoid deadloop
      wait(cfg.vif.rst_n === 1);
      seq_item_port.get_next_item(req);
      `uvm_info(`gfn, $sformatf("driver rcvd item:\n%0s", req.convert2string()), UVM_HIGH)
      if (!in_reset) begin
        if (cfg.agent_type == PushAgent) begin
          drive_push();
        end else if (cfg.agent_type == PullAgent) begin
          drive_pull();
        end else begin
          `uvm_fatal(`gfn, $sformatf("%0s is an invalid driver protocol!", cfg.agent_type))
        end
      end
      seq_item_port.item_done(req);
    end
  endtask

  // Drives device side of ready/valid protocol.
  virtual task drive_push();
    repeat (req.device_delay) begin
      if (in_reset) break;
      @(`PUSH_DRIVER);
    end
    if (!in_reset) begin
      `PUSH_DRIVER.ready_int  <= 1'b1;
      `PUSH_DRIVER.d_data_int <= req.d_data;
    end
    @(`PUSH_DRIVER);
    if (!in_reset) begin
      `PUSH_DRIVER.ready_int  <= 1'b0;
      if (!cfg.hold_d_data_until_next_req) `PUSH_DRIVER.d_data_int <= 'x;
    end
  endtask

  virtual task drive_pull();
    while (!`PULL_DRIVER.req && !in_reset) begin
      @(`PULL_DRIVER);
    end
    repeat (req.device_delay) begin
      if (in_reset) break;
      @(`PULL_DRIVER);
    end
    if (!in_reset) begin
      `PULL_DRIVER.ack_int    <= 1'b1;
      `PULL_DRIVER.d_data_int <= req.d_data;
    end
    @(`PULL_DRIVER);
    if (!in_reset) begin
      `PULL_DRIVER.ack_int    <= 1'b0;
      if (!cfg.hold_d_data_until_next_req) `PULL_DRIVER.d_data_int <= 'x;
    end
  endtask

endclass

`undef PULL_DRIVER
`undef PUSH_DRIVER
