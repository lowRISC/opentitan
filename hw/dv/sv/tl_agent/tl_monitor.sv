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

  tl_seq_item    pending_a_req[bit [SourceWidth - 1 : 0]];
  string         agent_name;
  uvm_phase      run_phase_h;

  uvm_analysis_port #(tl_seq_item) d_chan_port;
  uvm_analysis_port #(tl_seq_item) a_chan_port;
  // send back a chan info ASAP for device to support same cycle response
  uvm_analysis_port #(tl_seq_item) a_chan_same_cycle_rsp_port;

  `uvm_component_utils(tl_monitor)

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    d_chan_port = new("d_chan_port", this);
    a_chan_port = new("a_chan_port", this);
    a_chan_same_cycle_rsp_port = new("a_chan_same_cycle_rsp_port", this);
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

  // on reset flush pending request
  virtual task reset_thread();
    forever begin
      @(negedge cfg.vif.rst_n);
      cfg.reset_asserted = 1'b1;
      // on reset asserted sample pending request is present or not
      if (cfg.en_cov) cov.m_pending_req_on_rst_cg.sample(pending_a_req.size() != 0);
      @(posedge cfg.vif.rst_n);
      cfg.reset_asserted = 1'b0;
      pending_a_req.delete();
    end
  endtask : reset_thread

  virtual task a_channel_thread();
    tl_seq_item req, cloned_req;
    bit item_done = 0;
    forever begin
      bit valid_req_with_same_cycle_rsp;
      bit valid_req_with_diff_cycle_rsp;
      // Qualify req with same cycle rsp from device enabled.
      valid_req_with_same_cycle_rsp = cfg.device_can_rsp_on_same_cycle &&
                                      cfg.vif.h2d.a_valid && cfg.vif.d2h.a_ready;

      // Qualify req with same cycle rsp from device disabled.
      valid_req_with_diff_cycle_rsp = !cfg.device_can_rsp_on_same_cycle &&
                                      cfg.vif.mon_cb.h2d.a_valid && cfg.vif.mon_cb.d2h.a_ready;

      if (valid_req_with_same_cycle_rsp || valid_req_with_diff_cycle_rsp) begin
        tlul_pkg::tl_h2d_t h2d = valid_req_with_same_cycle_rsp ? cfg.vif.h2d : cfg.vif.mon_cb.h2d;

        req = tl_seq_item::type_id::create("req");
        req.a_addr   = h2d.a_address;
        req.a_opcode = h2d.a_opcode;
        req.a_size   = h2d.a_size;
        req.a_param  = h2d.a_param;
        req.a_data   = h2d.a_data;
        req.a_mask   = h2d.a_mask;
        req.a_source = h2d.a_source;
        `uvm_info("tl_logging", $sformatf("[%0s][a_chan] : %0s",
                   agent_name, req.convert2string()), UVM_HIGH)

        `downcast(cloned_req, req.clone());
        `DV_CHECK_EQ_FATAL(cloned_req.a_source >> cfg.valid_a_source_width, 0)
        `DV_CHECK_EQ_FATAL(pending_a_req.exists(cloned_req.a_source), 0)

        if (cfg.en_cov) sample_outstanding_cov(req);
        pending_a_req[cloned_req.a_source] = cloned_req;

        if (cfg.max_outstanding_req > 0 && cfg.vif.rst_n === 1) begin
          if (pending_a_req.size() > cfg.max_outstanding_req) begin
            `uvm_error(get_full_name(), $sformatf("Number of pending a_req exceeds limit %0d",
                                        pending_a_req.size()))
          end
          if (cfg.en_cov) cov.m_max_outstanding_cg.sample(pending_a_req.size());
        end

        // when device_can_rsp_on_same_cycle=1, write item to a_chan_same_cycle_rsp_port in the same
        // cycle a_valid & a_ready is high, then write to a_chan_port at the sample edge
        // when !device_can_rsp_on_same_cycle, only write to a_chan_port at the sample edge
        if (cfg.device_can_rsp_on_same_cycle) begin
          a_chan_same_cycle_rsp_port.write(req);
          // write to a_chan_port at the sample edge
          item_done = 1;
        end else begin
          a_chan_port.write(req);
        end
      end
      @(cfg.vif.mon_cb);
      if (cfg.device_can_rsp_on_same_cycle) begin
        if (item_done) begin
          a_chan_port.write(req);
          item_done = 0;
        end

        // sample within a cycle to allow device to respond in same cycle
        `DV_SPINWAIT_EXIT(
            #(cfg.time_a_valid_avail_after_sample_edge);,
            @(cfg.vif.mon_cb) `uvm_fatal(`gfn, $sformatf(
                "time_a_valid_avail_after_sample_edge (%0t) is over one cycle",
                cfg.time_a_valid_avail_after_sample_edge)))
      end
    end
  endtask : a_channel_thread

  // Collect ack from D channel
  virtual task d_channel_thread();
    tl_seq_item rsp;
    forever begin
      @(cfg.vif.mon_cb);
      if (cfg.vif.mon_cb.d2h.d_valid && cfg.vif.mon_cb.h2d.d_ready) begin
        // A matching request must exist
        `DV_CHECK_EQ_FATAL(pending_a_req.exists(cfg.vif.mon_cb.d2h.d_source), 1, $sformatf(
             "Cannot find request matching d_source 0x%0x", cfg.vif.mon_cb.d2h.d_source))
        rsp = pending_a_req[cfg.vif.mon_cb.d2h.d_source];
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
        pending_a_req.delete(cfg.vif.mon_cb.d2h.d_source);
        if (cfg.en_cov) cov.sample(rsp);
      end
    end
  endtask : d_channel_thread

  // update ok_to_end to prevent sim finish when there is any pending item
  virtual task monitor_ready_to_end();
    forever begin
      ok_to_end = (pending_a_req.size() == 0);
      if (ok_to_end) wait(pending_a_req.size() > 0);
      else           wait(pending_a_req.size() == 0);
    end
  endtask

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

  // sample outstanding related coverage
  virtual function void sample_outstanding_cov(tl_seq_item item);
    bit is_outstanding_item_w_same_addr;

    // check if same address has been used in more than 1 outstanding_item
    foreach (pending_a_req[i]) begin
      if (pending_a_req[i].a_addr == item.a_addr) begin
        is_outstanding_item_w_same_addr = 1;
        break;
      end
    end

    // sample a same address used in more than 1 outstanding items, if it's null, design doesn't
    // support outstanding items use the same address
    if (cov.m_outstanding_item_w_same_addr_cov_obj != null) begin
      cov.m_outstanding_item_w_same_addr_cov_obj.sample(is_outstanding_item_w_same_addr);
    end
  endfunction : sample_outstanding_cov

endclass : tl_monitor
