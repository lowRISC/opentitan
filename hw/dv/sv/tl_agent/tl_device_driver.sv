// Copyright lowRISC contributors (OpenTitan project).
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
    invalidate_d_channel();
    cfg.vif.d2h_int.a_ready <= 1'b0;
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
      int unsigned d_valid_delay, d_valid_len, d_valid_cnt;
      bit rsp_done, rsp_abort;
      seq_item_port.get_next_item(rsp);

      while (!rsp_done && !rsp_abort && cfg.vif.rst_n) begin
        if (cfg.use_seq_item_d_valid_delay) begin
          d_valid_delay = rsp.d_valid_delay;
        end else begin
          d_valid_delay = $urandom_range(cfg.d_valid_delay_min, cfg.d_valid_delay_max);
        end

        if (cfg.allow_d_valid_drop_wo_d_ready || rsp.rsp_abort_after_d_valid_len) begin
          if (cfg.use_seq_item_d_valid_len) begin
            d_valid_len = rsp.d_valid_len;
          end else begin
            d_valid_len = $urandom_range(cfg.d_valid_len_min, cfg.d_valid_len_max);
          end
        end

        // break delay loop if reset asserted to release blocking
        repeat (d_valid_delay) begin
          if (!cfg.vif.rst_n) break;
          else @(cfg.vif.device_cb);
        end
        if (cfg.vif.rst_n) begin
          cfg.vif.d2h_int.d_valid  <= 1'b1;
          cfg.vif.d2h_int.d_opcode <= tl_d_op_e'(rsp.d_opcode);
          cfg.vif.d2h_int.d_data   <= rsp.d_data;
          cfg.vif.d2h_int.d_source <= rsp.d_source;
          cfg.vif.d2h_int.d_param  <= rsp.d_param;
          cfg.vif.d2h_int.d_error  <= rsp.d_error;
          cfg.vif.d2h_int.d_sink   <= rsp.d_sink;
          cfg.vif.d2h_int.d_user   <= rsp.d_user;
          cfg.vif.d2h_int.d_size   <= rsp.d_size;
        end

        // wait for ready or reaching d_valid_len
        d_valid_cnt = 0;
        while (cfg.vif.rst_n) begin
          @(cfg.vif.device_cb);
          d_valid_cnt++;
          if (cfg.vif.device_cb.h2d.d_ready) begin
            rsp_done = 1;
            break;
          end else if ((cfg.allow_d_valid_drop_wo_d_ready || rsp.rsp_abort_after_d_valid_len)
                      && d_valid_cnt >= d_valid_len) begin
            if (rsp.rsp_abort_after_d_valid_len) rsp_abort = 1;
            invalidate_d_channel();
            if (!cfg.vif.rst_n) @(cfg.vif.device_cb);
            break;
          end
        end // while (!cfg.vif.rst_n)
      end // while (!rsp_done && cfg.vif.rst_n)
      invalidate_d_channel();
      rsp.rsp_completed = !rsp_abort;
      seq_item_port.item_done();
      seq_item_port.put_response(rsp);
    end
  endtask : d_channel_thread

  function void invalidate_d_channel();
    if (cfg.invalidate_d_x) begin
      cfg.vif.d2h_int.d_opcode <= tlul_pkg::tl_d_op_e'('x);
      cfg.vif.d2h_int.d_param <= '{default:'x};
      cfg.vif.d2h_int.d_size <= '{default:'x};
      cfg.vif.d2h_int.d_source <= '{default:'x};
      cfg.vif.d2h_int.d_sink <= '{default:'x};
      cfg.vif.d2h_int.d_data <= '{default:'x};
      cfg.vif.d2h_int.d_user <= '{default:'x};
      cfg.vif.d2h_int.d_error <= 1'bx;
      cfg.vif.d2h_int.d_valid <= 1'b0;
    end else begin // if (cfg.invalidate_d_x)
      tlul_pkg::tl_d2h_t d2h;
      `DV_CHECK_STD_RANDOMIZE_FATAL(d2h)
      d2h.d_valid = 1'b0;
      cfg.vif.d2h_int <= d2h;
    end
  endfunction : invalidate_d_channel

endclass
