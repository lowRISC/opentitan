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
    fork
      a_channel_thread();
      d_channel_thread();
      reset_thread();
    join_none
 endtask

  virtual task reset_thread();
    forever begin
      @(posedge cfg.vif.rst_n);
      // Check for seq_item_port FIFO is empty when coming out of reset
      `DV_CHECK_EQ(seq_item_port.has_do_available(), 0);
    end
  endtask : reset_thread

  virtual task reset_signals();
    invalidate_d_channel();
    cfg.vif.device_cb.d2h.a_ready <= 1'b0;
    @(posedge cfg.vif.device_cb.rst_n);
  endtask

  virtual task a_channel_thread();
    int unsigned ready_delay;
    forever begin
      ready_delay = $urandom_range(cfg.a_ready_delay_min, cfg.a_ready_delay_max);
      repeat(ready_delay) @(cfg.vif.device_cb);
      cfg.vif.device_cb.d2h.a_ready <= 1'b1;
      @(cfg.vif.device_cb);
      cfg.vif.device_cb.d2h.a_ready <= 1'b0;
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
      cfg.vif.device_cb.d2h.d_valid  <= 1'b1;
      cfg.vif.device_cb.d2h.d_opcode <= tl_d_op_e'(rsp.d_opcode);
      cfg.vif.device_cb.d2h.d_data   <= rsp.d_data;
      cfg.vif.device_cb.d2h.d_source <= rsp.d_source;
      cfg.vif.device_cb.d2h.d_param  <= rsp.d_param;
      cfg.vif.device_cb.d2h.d_error  <= rsp.d_error;
      cfg.vif.device_cb.d2h.d_sink   <= rsp.d_sink;
      cfg.vif.device_cb.d2h.d_user   <= rsp.d_user;
      cfg.vif.device_cb.d2h.d_size   <= rsp.d_size;
      // bypass delay in case of reset
      if (cfg.vif.rst_n) @(cfg.vif.device_cb);
      while (!cfg.vif.device_cb.h2d.d_ready && cfg.vif.rst_n) @(cfg.vif.device_cb);
      invalidate_d_channel();
      seq_item_port.item_done();
    end
  endtask : d_channel_thread

  function void invalidate_d_channel();
    cfg.vif.device_cb.d2h.d_opcode <= tlul_pkg::tl_d_op_e'('x);
    cfg.vif.device_cb.d2h.d_param <= '{default:'x};
    cfg.vif.device_cb.d2h.d_size <= '{default:'x};
    cfg.vif.device_cb.d2h.d_source <= '{default:'x};
    cfg.vif.device_cb.d2h.d_sink <= '{default:'x};
    cfg.vif.device_cb.d2h.d_data <= '{default:'x};
    cfg.vif.device_cb.d2h.d_user <= '{default:'x};
    cfg.vif.device_cb.d2h.d_error <= 1'bx;
    cfg.vif.device_cb.d2h.d_valid <= 1'b0;
  endfunction : invalidate_d_channel

endclass
