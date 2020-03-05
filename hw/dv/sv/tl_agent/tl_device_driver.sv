// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

// ---------------------------------------------
// TileLink device driver
// ---------------------------------------------
class tl_device_driver extends tl_base_driver;

  `uvm_component_utils(tl_device_driver)
  `uvm_component_new

  virtual task get_and_drive();
    // Wait for initial reset to pass.
    wait(cfg.vif.rst_n === 1'b0);
    wait(cfg.vif.rst_n === 1'b1);
    fork
      a_channel_thread();
      d_channel_thread();
    join_none
 endtask

  // reset signals every time reset occurs.
  virtual task reset_signals();
    forever begin
      @(negedge cfg.vif.rst_n);
      invalidate_d_channel();
      cfg.vif.d2h_int.a_ready <= 1'b0;
      // Check for seq_item_port FIFO is empty when coming out of reset
      `DV_CHECK_EQ(seq_item_port.has_do_available(), 0);
      @(posedge cfg.vif.rst_n);
    end
  endtask

  virtual task a_channel_thread();
    int unsigned ready_delay;

    forever begin
      ready_delay = $urandom_range(cfg.a_ready_delay_min, cfg.a_ready_delay_max);
      repeat(ready_delay) @(cfg.vif.device_cb);
      cfg.vif.device_cb.d2h_int.a_ready <= 1'b1;
      @(cfg.vif.device_cb);
      cfg.vif.device_cb.d2h_int.a_ready <= 1'b0;
    end
  endtask

  virtual task d_channel_thread();
    bit req_found;
    tl_seq_item rsp;

    forever begin
      int unsigned d_valid_delay;
      seq_item_port.get_next_item(rsp);
      if (cfg.use_seq_item_d_valid_delay) begin
        d_valid_delay = rsp.d_valid_delay;
      end else begin
        d_valid_delay = $urandom_range(cfg.d_valid_delay_min, cfg.d_valid_delay_max);
      end
      // break delay loop if reset asserted to release blocking
      repeat (d_valid_delay) begin
        if (!cfg.vif.rst_n) break;
        else @(cfg.vif.device_cb);
      end
      if (cfg.vif.rst_n) begin
        cfg.vif.device_cb.d2h_int.d_valid  <= 1'b1;
        cfg.vif.device_cb.d2h_int.d_opcode <= tl_d_op_e'(rsp.d_opcode);
        cfg.vif.device_cb.d2h_int.d_data   <= rsp.d_data;
        cfg.vif.device_cb.d2h_int.d_source <= rsp.d_source;
        cfg.vif.device_cb.d2h_int.d_param  <= rsp.d_param;
        cfg.vif.device_cb.d2h_int.d_error  <= rsp.d_error;
        cfg.vif.device_cb.d2h_int.d_sink   <= rsp.d_sink;
        cfg.vif.device_cb.d2h_int.d_user   <= rsp.d_user;
        cfg.vif.device_cb.d2h_int.d_size   <= rsp.d_size;
        // bypass delay in case of reset
        @(cfg.vif.device_cb);
      end
      while (!cfg.vif.device_cb.h2d.d_ready && cfg.vif.rst_n) @(cfg.vif.device_cb);
      invalidate_d_channel();
      seq_item_port.item_done();
    end
  endtask : d_channel_thread

  function void invalidate_d_channel();
    cfg.vif.d2h_int.d_opcode <= tlul_pkg::tl_d_op_e'('x);
    cfg.vif.d2h_int.d_param <= '{default:'x};
    cfg.vif.d2h_int.d_size <= '{default:'x};
    cfg.vif.d2h_int.d_source <= '{default:'x};
    cfg.vif.d2h_int.d_sink <= '{default:'x};
    cfg.vif.d2h_int.d_data <= '{default:'x};
    cfg.vif.d2h_int.d_user <= '{default:'x};
    cfg.vif.d2h_int.d_error <= 1'bx;
    cfg.vif.d2h_int.d_valid <= 1'b0;
  endfunction : invalidate_d_channel

endclass
