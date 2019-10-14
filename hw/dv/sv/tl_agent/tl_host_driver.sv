// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

// ---------------------------------------------
// TileLink host driver
// ---------------------------------------------
class tl_host_driver extends uvm_driver#(tl_seq_item);

  virtual tl_if  vif;
  tl_seq_item    pending_a_req[$];
  tl_agent_cfg   cfg;
  bit reset_asserted;

  `uvm_component_utils(tl_host_driver)

  function new (string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(virtual tl_if)::get(this, "", "vif", vif)) begin
      `uvm_fatal("NO_VIF", {"virtual interface must be set for:",
        get_full_name(),".vif"});
    end
    if (!uvm_config_db#(tl_agent_cfg)::get(this, "", "cfg", cfg)) begin
      `uvm_fatal("NO_CFG", {"cfg must be set for:", get_full_name(),".cfg"});
    end
  endfunction : build_phase

  virtual task run_phase(uvm_phase phase);
    wait_for_reset_done();
    fork
      begin : process_seq_item
        forever begin
          seq_item_port.try_next_item(req);
          if (req != null) begin
            send_a_channel_request(req);
          end else begin
            @(vif.host_cb);
          end
        end
      end
      d_channel_thread();
      reset_thread();
    join_none
  endtask : run_phase

  virtual task reset_thread();
    forever begin
      @(negedge vif.rst_n);
      reset_asserted = 1'b1;
      @(posedge vif.rst_n == 1);
      reset_asserted = 1'b0;
      // Check for seq_item_port FIFO & pending req queue is empty when coming out of reset
      `DV_CHECK_EQ(pending_a_req.size(), 0)
      `DV_CHECK_EQ(seq_item_port.has_do_available(), 0);
    end
  endtask : reset_thread

  virtual task wait_for_reset_done();
    vif.host_cb.h2d.a_valid <= 1'b0;
    vif.host_cb.h2d.d_ready <= 1'b0;
    @(posedge vif.host_cb.rst_n);
    // wait a clk to make sure a_channel a_valid stay high for a clk cycle if a_valid_delay = 0
    @(vif.host_cb);
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
      else @(vif.host_cb);
    end
    // wait until no outstanding transaction with same source id
    while (is_source_in_pending_req(req.a_source) & !reset_asserted) @(vif.host_cb);
    vif.host_cb.h2d.a_address <= req.a_addr;
    vif.host_cb.h2d.a_opcode  <= req.a_opcode;
    vif.host_cb.h2d.a_size    <= req.a_size;
    vif.host_cb.h2d.a_param   <= req.a_param;
    vif.host_cb.h2d.a_data    <= req.a_data;
    vif.host_cb.h2d.a_mask    <= req.a_mask;
    vif.host_cb.h2d.a_user    <= '0;
    vif.host_cb.h2d.a_source  <= req.a_source;
    vif.host_cb.h2d.a_valid   <= 1'b1;
    // bypass delay in case of reset
    if (!reset_asserted) @(vif.host_cb);
    while(!vif.host_cb.d2h.a_ready && !reset_asserted) @(vif.host_cb);
    vif.host_cb.h2d.a_valid   <= 1'b0;
    seq_item_port.item_done();
    pending_a_req.push_back(req);
    `uvm_info(get_full_name(), $sformatf("Req sent: %0s", req.convert2string()), UVM_HIGH)
    while((cfg.max_outstanding_req > 0) &&
          (pending_a_req.size() >= cfg.max_outstanding_req) && !reset_asserted) begin
      @(vif.host_cb);
    end
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
        else @(vif.host_cb);
      end
      vif.host_cb.h2d.d_ready <= 1'b1;
      if (!(reset_asserted & (pending_a_req.size() != 0))) @(vif.host_cb);
      if (vif.host_cb.d2h.d_valid | ((pending_a_req.size() != 0) & reset_asserted)) begin
        // Use the source ID to find the matching request
        foreach (pending_a_req[i]) begin
          if ((pending_a_req[i].a_source == vif.host_cb.d2h.d_source) | reset_asserted) begin
            rsp = pending_a_req[i];
            rsp.d_opcode = vif.host_cb.d2h.d_opcode;
            rsp.d_data   = vif.host_cb.d2h.d_data;
            rsp.d_source = vif.host_cb.d2h.d_source;
            rsp.d_param  = vif.host_cb.d2h.d_param;
            rsp.d_error  = vif.host_cb.d2h.d_error;
            rsp.d_sink   = vif.host_cb.d2h.d_sink;
            rsp.d_size   = vif.host_cb.d2h.d_size;
            rsp.d_user   = vif.host_cb.d2h.d_user;
            req_found = 1'b1;
            seq_item_port.put_response(rsp);
            pending_a_req.delete(i);
            `uvm_info(get_full_name(), $sformatf("Got response %0s, pending req:%0d",
                                       rsp.convert2string(), pending_a_req.size()), UVM_HIGH)
            if (!reset_asserted) break;
          end
        end

        if (!req_found) begin
          `uvm_error(get_full_name(), $sformatf(
                     "Cannot find request matching d_source 0x%0x", vif.host_cb.d2h.d_source))
        end
      end
      vif.host_cb.h2d.d_ready <= 1'b0;
    end
  endtask : d_channel_thread

  function bit is_source_in_pending_req(bit [SourceWidth-1 : 0] source);
    foreach (pending_a_req[i]) begin
      if (pending_a_req[i].a_source == source) return 1;
    end
    return 0;
  endfunction
endclass : tl_host_driver
