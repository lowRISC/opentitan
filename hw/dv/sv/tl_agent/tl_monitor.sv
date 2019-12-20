// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

// ---------------------------------------------
// TileLink interface monitor
// ---------------------------------------------

// TODO: Implement protocl check in the monitor
class tl_monitor extends dv_base_monitor#(
    .ITEM_T (tl_seq_item),
    .CFG_T  (tl_agent_cfg),
    .COV_T  (tl_agent_cov)
  );

  tl_seq_item    pending_a_req[$];
  string         agent_name;
  bit            objection_raised;
  uvm_phase      run_phase_h;

  uvm_analysis_port #(tl_seq_item) d_chan_port;
  uvm_analysis_port #(tl_seq_item) a_chan_port;

  `uvm_component_utils(tl_monitor)

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    d_chan_port = new("d_chan_port", this);
    a_chan_port = new("a_chan_port", this);
  endfunction : build_phase

  virtual task run_phase(uvm_phase phase);
    run_phase_h = phase;
    wait_for_reset_done();
    fork
      a_channel_thread();
      d_channel_thread();
      reset_thread();
    join_none
  endtask : run_phase

  virtual task wait_for_reset_done();
    @(posedge cfg.vif.rst_n);
  endtask : wait_for_reset_done

  // on reset flush pending request and drop objection
  virtual task reset_thread();
    forever begin
      @(negedge cfg.vif.rst_n);
      // on reset asserted sample pending request is present or not
      if (cfg.en_cov) cov.pending_req_on_rst_cg.sample(pending_a_req.size() != 0);
      @(posedge cfg.vif.rst_n);
      pending_a_req.delete();
      if (objection_raised) begin
        run_phase_h.drop_objection(this);
        objection_raised = 1'b0;
      end
    end
  endtask : reset_thread

  virtual task a_channel_thread();
    tl_seq_item req;
    forever begin
      if (cfg.vif.mon_cb.h2d.a_valid && cfg.vif.mon_cb.d2h.a_ready) begin
        req = tl_seq_item::type_id::create("req");
        req.a_addr   = cfg.vif.mon_cb.h2d.a_address;
        req.a_opcode = cfg.vif.mon_cb.h2d.a_opcode;
        req.a_size   = cfg.vif.mon_cb.h2d.a_size;
        req.a_param  = cfg.vif.mon_cb.h2d.a_param;
        req.a_data   = cfg.vif.mon_cb.h2d.a_data;
        req.a_mask   = cfg.vif.mon_cb.h2d.a_mask;
        req.a_source = cfg.vif.mon_cb.h2d.a_source;
        `uvm_info("tl_logging", $sformatf("[%0s][a_chan] : %0s",
                   agent_name, req.convert2string()), UVM_HIGH)
        a_chan_port.write(req);
        pending_a_req.push_back(req);
        if (cfg.max_outstanding_req > 0) begin
          if (pending_a_req.size() > cfg.max_outstanding_req) begin
            `uvm_error(get_full_name(), $sformatf("Number of pending a_req exceeds limit %0d",
                                        pending_a_req.size()))
          end
          if (cfg.en_cov) cov.max_outstanding_cg.sample(pending_a_req.size());
        end
        if (!objection_raised) begin
          run_phase_h.raise_objection(this);
          objection_raised = 1'b1;
        end
      end
      @(cfg.vif.mon_cb);
    end
  endtask : a_channel_thread

  // Collect ack from D channel
  virtual task d_channel_thread();
    tl_seq_item rsp;
    forever begin
      @(cfg.vif.mon_cb);
      if (cfg.vif.mon_cb.d2h.d_valid && cfg.vif.mon_cb.h2d.d_ready) begin
        // Use the source ID to find the matching request
        bit req_found;
        foreach (pending_a_req[i]) begin
          if (pending_a_req[i].a_source == cfg.vif.mon_cb.d2h.d_source) begin
            rsp = pending_a_req[i];
            rsp.d_opcode = cfg.vif.mon_cb.d2h.d_opcode;
            rsp.d_data   = cfg.vif.mon_cb.d2h.d_data;
            rsp.d_source = cfg.vif.mon_cb.d2h.d_source;
            rsp.d_param  = cfg.vif.mon_cb.d2h.d_param;
            rsp.d_error  = cfg.vif.mon_cb.d2h.d_error;
            rsp.d_sink   = cfg.vif.mon_cb.d2h.d_sink;
            rsp.d_size   = cfg.vif.mon_cb.d2h.d_size;
            rsp.d_user   = cfg.vif.mon_cb.d2h.d_user;
            `uvm_info("tl_logging", $sformatf("[%0s][d_chan] : %0s",
                      agent_name, rsp.convert2string()), UVM_HIGH)
            d_chan_port.write(rsp);
            pending_a_req.delete(i);
            if (pending_a_req.size() == 0) begin
              run_phase_h.drop_objection(this);
              objection_raised = 1'b0;
            end
            req_found = 1'b1;
            break;
          end
        end
        if (!req_found) begin
          `uvm_error(get_full_name(), $sformatf(
             "Cannot find request matching d_source 0x%0x", cfg.vif.mon_cb.d2h.d_source))
        end
      end
    end
  endtask : d_channel_thread

  virtual function void report_phase(uvm_phase phase);
    if (pending_a_req.size() > 0) begin
      `uvm_error(get_full_name(), $sformatf(
                 "%0d items left at the end of sim", pending_a_req.size()))
      foreach (pending_a_req[i]) begin
        `uvm_info(get_full_name(), $sformatf("pending_a_req[%0d] = %0s",
                  i, pending_a_req[i].convert2string()), UVM_LOW)
      end
    end
  endfunction : report_phase

endclass : tl_monitor
