// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

// ---------------------------------------------
// TileLink host driver
// ---------------------------------------------
class tl_host_driver extends tl_base_driver;

  tl_seq_item    pending_a_req[$];
  bit reset_asserted;

  `uvm_component_utils(tl_host_driver)
  `uvm_component_new

  virtual task get_and_drive();
    fork
      begin : process_seq_item
        forever begin
          seq_item_port.try_next_item(req);
          if (req != null) begin
            send_a_channel_request(req);
          end else begin
            @(cfg.vif.host_cb);
          end
        end
      end
      d_channel_thread();
      reset_thread();
    join_none
  endtask

  virtual task reset_thread();
    forever begin
      @(negedge cfg.vif.rst_n);
      reset_asserted = 1'b1;
      @(posedge cfg.vif.rst_n == 1);
      reset_asserted = 1'b0;
      // Check for seq_item_port FIFO & pending req queue is empty when coming out of reset
      `DV_CHECK_EQ(pending_a_req.size(), 0)
      `DV_CHECK_EQ(seq_item_port.has_do_available(), 0);
    end
  endtask : reset_thread

  virtual task reset_signals();
    invalidate_a_channel();
    cfg.vif.host_cb.h2d.d_ready <= 1'b0;
    @(posedge cfg.vif.host_cb.rst_n);
    // wait a clk to make sure a_channel a_valid stay high for a clk cycle if a_valid_delay = 0
    @(cfg.vif.host_cb);
  endtask

  // Send request on A channel
  virtual task send_a_channel_request(tl_seq_item req);
    int unsigned a_valid_delay;
    if (cfg.use_seq_item_a_valid_delay) begin
      a_valid_delay = req.a_valid_delay;
    end else begin
      a_valid_delay = $urandom_range(cfg.a_valid_delay_min, cfg.a_valid_delay_max);
    end
    // break delay loop if reset asserted to release blocking
    repeat (a_valid_delay) begin
      if (reset_asserted) break;
      else @(cfg.vif.host_cb);
    end
    // wait until no outstanding transaction with same source id
    while (is_source_in_pending_req(req.a_source) & !reset_asserted) @(cfg.vif.host_cb);
    cfg.vif.host_cb.h2d.a_address <= req.a_addr;
    cfg.vif.host_cb.h2d.a_opcode  <= tl_a_op_e'(req.a_opcode);
    cfg.vif.host_cb.h2d.a_size    <= req.a_size;
    cfg.vif.host_cb.h2d.a_param   <= req.a_param;
    cfg.vif.host_cb.h2d.a_data    <= req.a_data;
    cfg.vif.host_cb.h2d.a_mask    <= req.a_mask;
    cfg.vif.host_cb.h2d.a_user    <= '0;
    cfg.vif.host_cb.h2d.a_source  <= req.a_source;
    cfg.vif.host_cb.h2d.a_valid   <= 1'b1;
    // bypass delay in case of reset
    if (!reset_asserted) @(cfg.vif.host_cb);
    while(!cfg.vif.host_cb.d2h.a_ready && !reset_asserted) @(cfg.vif.host_cb);
    invalidate_a_channel();
    seq_item_port.item_done();
    if (reset_asserted) seq_item_port.put_response(req); // if reset, skip data phase
    else                pending_a_req.push_back(req);
    `uvm_info(get_full_name(), $sformatf("Req sent: %0s", req.convert2string()), UVM_HIGH)
  endtask : send_a_channel_request

  // Collect ack from D channel
  virtual task d_channel_thread();
    int unsigned d_ready_delay;
    tl_seq_item rsp;
    forever begin
      bit req_found;
      d_ready_delay = $urandom_range(cfg.d_ready_delay_min, cfg.d_ready_delay_max);
      // break delay loop if reset asserted to release blocking
      repeat (d_ready_delay) begin
        if (reset_asserted & (pending_a_req.size() != 0)) break;
        else @(cfg.vif.host_cb);
      end
      cfg.vif.host_cb.h2d.d_ready <= 1'b1;
      if (!(reset_asserted & (pending_a_req.size() != 0))) @(cfg.vif.host_cb);
      if (cfg.vif.host_cb.d2h.d_valid | ((pending_a_req.size() != 0) & reset_asserted)) begin
        // Use the source ID to find the matching request
        foreach (pending_a_req[i]) begin
          if ((pending_a_req[i].a_source == cfg.vif.host_cb.d2h.d_source) | reset_asserted) begin
            rsp = pending_a_req[i];
            rsp.d_opcode = cfg.vif.host_cb.d2h.d_opcode;
            rsp.d_data   = cfg.vif.host_cb.d2h.d_data;
            rsp.d_param  = cfg.vif.host_cb.d2h.d_param;
            rsp.d_error  = cfg.vif.host_cb.d2h.d_error;
            rsp.d_sink   = cfg.vif.host_cb.d2h.d_sink;
            rsp.d_size   = cfg.vif.host_cb.d2h.d_size;
            rsp.d_user   = cfg.vif.host_cb.d2h.d_user;
            // make sure every req has a rsp with same source even during reset
            if (reset_asserted) rsp.d_source = rsp.a_source;
            else                rsp.d_source = cfg.vif.host_cb.d2h.d_source;
            req_found = 1'b1;
            seq_item_port.put_response(rsp);
            pending_a_req.delete(i);
            `uvm_info(get_full_name(), $sformatf("Got response %0s, pending req:%0d",
                                       rsp.convert2string(), pending_a_req.size()), UVM_HIGH)
            break;
          end
        end

        if (!req_found) begin
          `uvm_error(get_full_name(), $sformatf(
                     "Cannot find request matching d_source 0x%0x", cfg.vif.host_cb.d2h.d_source))
        end
      end
      cfg.vif.host_cb.h2d.d_ready <= 1'b0;
    end
  endtask : d_channel_thread

  function bit is_source_in_pending_req(bit [SourceWidth-1 : 0] source);
    foreach (pending_a_req[i]) begin
      if (pending_a_req[i].a_source == source) return 1;
    end
    return 0;
  endfunction

  function void invalidate_a_channel();
    cfg.vif.host_cb.h2d.a_opcode <= tlul_pkg::tl_a_op_e'('x);
    cfg.vif.host_cb.h2d.a_param <= '{default:'x};
    cfg.vif.host_cb.h2d.a_size <= '{default:'x};
    cfg.vif.host_cb.h2d.a_source <= '{default:'x};
    cfg.vif.host_cb.h2d.a_address <= '{default:'x};
    cfg.vif.host_cb.h2d.a_mask <= '{default:'x};
    cfg.vif.host_cb.h2d.a_data <= '{default:'x};
    cfg.vif.host_cb.h2d.a_user <= '{default:'x};
    cfg.vif.host_cb.h2d.a_valid <= 1'b0;
  endfunction : invalidate_a_channel

endclass : tl_host_driver
