// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

// ---------------------------------------------
// TileLink host driver
// ---------------------------------------------
class tl_host_driver extends tl_base_driver;

  tl_seq_item pending_a_req[$];
  bit reset_asserted;

  `uvm_component_utils(tl_host_driver)
  `uvm_component_new

  virtual task get_and_drive();
    // Wait for initial reset to pass.
    wait(cfg.vif.rst_n === 1'b0);
    wait(cfg.vif.rst_n === 1'b1);
    fork
      begin : process_seq_item
        forever begin
          seq_item_port.try_next_item(req);
          if (req != null) begin
            send_a_channel_request(req);
          end else begin
            // wait for reset to deassert and always align with clock edge to send item
            wait(cfg.vif.rst_n === 1'b1);
            `DV_SPINWAIT_EXIT(@(cfg.vif.host_cb);,
                              wait(reset_asserted);)
          end
        end
      end
      d_channel_thread();
      d_ready_rsp();
    join_none
  endtask

  // reset signals every time reset occurs.
  virtual task reset_signals();
    forever begin
      @(negedge cfg.vif.rst_n);
      reset_asserted = 1'b1;
      invalidate_a_channel();
      cfg.vif.h2d_int.d_ready <= 1'b0;
      @(posedge cfg.vif.rst_n);
      reset_asserted = 1'b0;
      // Check for seq_item_port FIFO & pending req queue is empty when coming out of reset
      `DV_CHECK_EQ(pending_a_req.size(), 0)
      `DV_CHECK_EQ(seq_item_port.has_do_available(), 0)
      // Check if the a_source_pend_q maintained in the cfg is empty.
      `DV_CHECK_EQ(cfg.a_source_pend_q.size(), 0)
    end
  endtask

  // Send request on A channel
  virtual task send_a_channel_request(tl_seq_item req);
    int unsigned a_valid_delay, a_valid_len;
    bit req_done, req_abort;

    // Seq may override the a_source or all valid sources are used but still send req, in which case
    // it is possible that it might not have factored
    // This wait is only needed in xbar test as xbar can use all valid sources and xbar_stress runs
    // all seq in parallel, which needs driver to stall when the source is currently being used
    // in the a_source values from pending requests that have not yet completed. If that is true, we
    // need to insert additional delays to ensure we do not end up sending the new request whose
    // a_source matches one of the pending requests.
    `DV_SPINWAIT_EXIT(while (is_source_in_pending_req(req.a_source)) @(cfg.vif.host_cb);,
                      wait(reset_asserted);)

    while (!req_done && !req_abort) begin
      if (cfg.use_seq_item_a_valid_delay) begin
        a_valid_delay = req.a_valid_delay;
      end else begin
        a_valid_delay = $urandom_range(cfg.a_valid_delay_min, cfg.a_valid_delay_max);
      end

      if (req.req_abort_after_a_valid_len || cfg.allow_a_valid_drop_wo_a_ready) begin
        if (cfg.use_seq_item_a_valid_len) begin
          a_valid_len = req.a_valid_len;
        end else begin
          a_valid_len = $urandom_range(cfg.a_valid_len_min, cfg.a_valid_len_max);
        end
      end

      // break delay loop if reset asserted to release blocking
      `DV_SPINWAIT_EXIT(repeat (a_valid_delay) @(cfg.vif.host_cb);,
                        wait(reset_asserted);)

      if (!reset_asserted) begin
        pending_a_req.push_back(req);
        cfg.vif.host_cb.h2d_int.a_address <= req.a_addr;
        cfg.vif.host_cb.h2d_int.a_opcode  <= tl_a_op_e'(req.a_opcode);
        cfg.vif.host_cb.h2d_int.a_size    <= req.a_size;
        cfg.vif.host_cb.h2d_int.a_param   <= req.a_param;
        cfg.vif.host_cb.h2d_int.a_data    <= req.a_data;
        cfg.vif.host_cb.h2d_int.a_mask    <= req.a_mask;
        cfg.vif.host_cb.h2d_int.a_user    <= '0;
        cfg.vif.host_cb.h2d_int.a_source  <= req.a_source;
        cfg.vif.host_cb.h2d_int.a_valid   <= 1'b1;
      end else begin
        req_abort = 1;
      end
      // drop valid if it lasts for a_valid_len, even there is no a_ready
      `DV_SPINWAIT_EXIT(send_a_request_body(req, a_valid_len, req_done, req_abort);,
                        wait(reset_asserted);)

      // when reset and host_cb.h2d_int.a_valid <= 1 occur at the same time, if clock is off,
      // there is a race condition and invalidate_a_channel can't clear a_valid.
      if (reset_asserted) cfg.vif.host_cb.h2d_int.a_valid <= 1'b0;
      invalidate_a_channel();
    end
    seq_item_port.item_done();
    if (req_abort || reset_asserted) begin
      req.req_completed = 0;
      // Just wire the d_source back to a_source to avoid errors in upstream logic.
      req.d_source = req.a_source;
      seq_item_port.put_response(req);
    end else begin
      req.req_completed = 1;
    end
    `uvm_info(get_full_name(), $sformatf("Req %0s: %0s", req_abort ? "aborted" : "sent",
                                         req.convert2string()), UVM_HIGH)
  endtask : send_a_channel_request

  virtual task send_a_request_body(tl_seq_item req, int a_valid_len,
                                   ref bit req_done, ref bit req_abort);
    int unsigned a_valid_cnt;
    while (1) begin
      @(cfg.vif.host_cb);
      a_valid_cnt++;
      if (cfg.vif.host_cb.d2h.a_ready) begin
        req_done = 1;
        break;
      end else if ((req.req_abort_after_a_valid_len || cfg.allow_a_valid_drop_wo_a_ready) &&
                   a_valid_cnt >= a_valid_len) begin
        if (req.req_abort_after_a_valid_len) req_abort = 1;
        cfg.vif.host_cb.h2d_int.a_valid <= 1'b0;
        // remove unaccepted item
        void'(pending_a_req.pop_back());
        invalidate_a_channel();
        @(cfg.vif.host_cb);
        break;
      end
    end
  endtask : send_a_request_body

  // host responds d_ready
  virtual task d_ready_rsp();
    int unsigned d_ready_delay;
    tl_seq_item rsp;

    forever begin
      bit req_found;
      d_ready_delay = $urandom_range(cfg.d_ready_delay_min, cfg.d_ready_delay_max);
      // if a_valid high then d_ready must be high, exit the delay when a_valid is set
      `DV_SPINWAIT_EXIT(repeat (d_ready_delay) @(cfg.vif.host_cb);,
         wait(!cfg.host_can_stall_rsp_when_a_valid_high && cfg.vif.h2d_int.a_valid))

      cfg.vif.host_cb.h2d_int.d_ready <= 1'b1;
      @(cfg.vif.host_cb);
      cfg.vif.host_cb.h2d_int.d_ready <= 1'b0;
    end
  endtask : d_ready_rsp

  // Collect ack from D channel
  virtual task d_channel_thread();
    int unsigned d_ready_delay;
    tl_seq_item rsp;

    forever begin
      bit req_found;

      if ((cfg.vif.host_cb.d2h.d_valid && cfg.vif.h2d_int.d_ready && !reset_asserted) ||
          ((pending_a_req.size() != 0) & reset_asserted)) begin
        // Use the source ID to find the matching request
        foreach (pending_a_req[i]) begin
          if ((pending_a_req[i].a_source == cfg.vif.host_cb.d2h.d_source) | reset_asserted) begin
            rsp = pending_a_req[i];
            rsp.d_opcode = cfg.vif.host_cb.d2h.d_opcode;
            rsp.d_data   = cfg.vif.host_cb.d2h.d_data;
            rsp.d_param  = cfg.vif.host_cb.d2h.d_param;
            rsp.d_sink   = cfg.vif.host_cb.d2h.d_sink;
            rsp.d_size   = cfg.vif.host_cb.d2h.d_size;
            rsp.d_user   = cfg.vif.host_cb.d2h.d_user;
            // set d_error = 0 and rsp_completed = 0 when reset occurs
            rsp.d_error  = reset_asserted ? 0 : cfg.vif.host_cb.d2h.d_error;
            // make sure every req has a rsp with same source even during reset
            if (reset_asserted) rsp.d_source = rsp.a_source;
            else                rsp.d_source = cfg.vif.host_cb.d2h.d_source;
            seq_item_port.put_response(rsp);
            pending_a_req.delete(i);
            `uvm_info(get_full_name(), $sformatf("Got response %0s, pending req:%0d",
                                       rsp.convert2string(), pending_a_req.size()), UVM_HIGH)
            req_found         = 1;
            rsp.rsp_completed = !reset_asserted;
            break;
          end
        end

        if (!req_found && !reset_asserted) begin
          `uvm_error(get_full_name(), $sformatf(
                     "Cannot find request matching d_source 0x%0x", cfg.vif.host_cb.d2h.d_source))
        end
      end else if (reset_asserted) begin
        wait(!reset_asserted);
      end
      `DV_SPINWAIT_EXIT(@(cfg.vif.host_cb);,
                        wait(reset_asserted);)
    end
  endtask : d_channel_thread

  function bit is_source_in_pending_req(bit [SourceWidth-1:0] source);
    foreach (pending_a_req[i]) begin
      if (pending_a_req[i].a_source == source) return 1;
    end
    return 0;
  endfunction

  function void invalidate_a_channel();
    cfg.vif.h2d_int.a_opcode <= tlul_pkg::tl_a_op_e'('x);
    cfg.vif.h2d_int.a_param <= '{default:'x};
    cfg.vif.h2d_int.a_size <= '{default:'x};
    cfg.vif.h2d_int.a_source <= '{default:'x};
    cfg.vif.h2d_int.a_address <= '{default:'x};
    cfg.vif.h2d_int.a_mask <= '{default:'x};
    cfg.vif.h2d_int.a_data <= '{default:'x};
    cfg.vif.h2d_int.a_user <= '{default:'x};
    cfg.vif.h2d_int.a_valid <= 1'b0;
  endfunction : invalidate_a_channel

endclass : tl_host_driver
