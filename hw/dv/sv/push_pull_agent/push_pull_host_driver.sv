// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`define PUSH_DRIVER cfg.vif.host_push_cb
`define PULL_DRIVER cfg.vif.host_pull_cb

class push_pull_host_driver #(parameter int DataWidth = 32) extends push_pull_driver #(DataWidth);

  `uvm_component_param_utils(push_pull_host_driver#(DataWidth))

  // the base class provides the following handles for use:
  // push_pull_agent_cfg: cfg

  `uvm_component_new

  virtual task do_reset();
    if (cfg.agent_type == PushAgent) begin
      cfg.vif.valid_int <= '0;
      cfg.vif.data_int  <= 'x;
    end else begin
      cfg.vif.req_int   <= '0;
    end
  endtask

  // drive trans received from sequencer
  virtual task get_and_drive();
    // wait for the initial reset to pass
    @(posedge cfg.vif.rst_n);
    forever begin
      seq_item_port.try_next_item(req);
      if (req != null) begin
        `uvm_info(`gfn, $sformatf("rcvd item:\n%0s", req.convert2string()), UVM_HIGH)
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
      end else begin
        cfg.vif.wait_clks(1);
      end
    end
  endtask

  // Drives host side of ready/valid protocol
  virtual task drive_push();
    repeat (req.host_delay) begin
      if (in_reset) break;
      @(`PUSH_DRIVER);
    end
    if (!in_reset) begin
      `PUSH_DRIVER.valid_int <= 1'b1;
      `PUSH_DRIVER.data      <= req.data;
    end
    do begin
      @(`PUSH_DRIVER);
    end while (!`PUSH_DRIVER.ready && !in_reset);
    if (!in_reset) begin
      `PUSH_DRIVER.valid_int <= 1'b0;
      `PUSH_DRIVER.data      <= 'x;
    end
  endtask

  // Drives host side of req/ack protocol
  virtual task drive_pull();
    repeat (req.host_delay) begin
      if (in_reset) break;
      @(`PULL_DRIVER);
    end
    if (!in_reset) begin
      `PULL_DRIVER.req_int <= 1'b1;
    end
    do begin
      @(`PULL_DRIVER);
    end while (!`PULL_DRIVER.ack && !in_reset);
    if (!in_reset) begin
      `PULL_DRIVER.req_int <= 1'b0;
    end
  endtask

endclass

`undef PULL_DRIVER
`undef PUSH_DRIVER
