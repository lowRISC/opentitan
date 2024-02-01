// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

// ---------------------------------------------
// TileLink interface monitor
// ---------------------------------------------
class tl_monitor extends dv_base_monitor#(
    .ITEM_T (tl_seq_item),
    .CFG_T  (tl_agent_cfg),
    .COV_T  (tl_agent_cov)
  );

  tl_seq_item    pending_a_req[bit [SourceWidth - 1 : 0]];
  string         agent_name;
  uvm_phase      run_phase_h;

  // Sequence items for transactions on the A and D channels. Sampled on the positive clock edge.
  //
  // If cfg.synchronise_ports (disabled by default), use these by waiting on channel_dir_port. This
  // gets updated just after we push to a_chan_port or d_chan_port, telling the reader which channel
  // to read. That way, the reader can guarantee a sample order if an A and D transaction both
  // appear at the same time.
  //
  // Otherwise, wait on a_chan_port and d_chan_port with two concurrent processes. A and D
  // transactions that happen at the same time will be popped from the fifos in an indeterminate
  // order.
  uvm_analysis_port #(tl_channels_e) channel_dir_port;
  uvm_analysis_port #(tl_seq_item)   a_chan_port;
  uvm_analysis_port #(tl_seq_item)   d_chan_port;

  // Sequence items for transactions on the A channel, sampled shortly after the positive clock
  // edge. This is only used if cfg.device_can_rsp_on_same_cycle, in which case a sequence item for
  // a transaction will appear on this port when sampled and on a_chan_port on the following clock
  // edge.
  uvm_analysis_port #(tl_seq_item) a_chan_same_cycle_rsp_port;

  `uvm_component_utils(tl_monitor)

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (cfg.synchronise_ports) begin
      channel_dir_port = new("channel_dir_port", this);
    end

    a_chan_port = new("a_chan_port", this);
    d_chan_port = new("d_chan_port", this);

    if (cfg.device_can_rsp_on_same_cycle) begin
      a_chan_same_cycle_rsp_port = new("a_chan_same_cycle_rsp_port", this);
    end
  endfunction : build_phase

  virtual task run_phase(uvm_phase phase);
    run_phase_h = phase;
    wait_for_reset_done();
    fork
      ad_channels_thread();
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

  // Check the A and D channels for transactions. When a transaction is seen, push it to a_chan_port
  // or d_chan_port, respectively. If cfg.synchronise_ports, also push the channel to
  // channel_dir_port. If transactions are seen for both channels on a clock edge, push D then A.
  //
  // If the device isn't expected to respond combinatorially (cfg.device_can_rsp_on_same_cycle = 0),
  // then both channels are sampled on the posedge of the clock. If the device *can* respond
  // combinatorially, we delay sampling on the A side by a short time. The idea is that the A
  // transaction will be asserted just after a clock edge and then D will be asserted some time
  // afterwards. Sampling A in the middle of the cycle and then D at the following clock ensures
  // that we see A before D (the order in which the events happened).
  task ad_channels_thread();

    // The most recently seen request on the A channel. Set to something non-null by successful
    // calls to check_a_channel. Cleared back to null when the item is written to a_chan_port.
    tl_seq_item a_chan_req_item;

    forever begin
      @(cfg.vif.mon_cb);
      // This is just after the clock edge, so time to sample D and A channels.

      // Handle the D side.
      check_d_channel();

      // Handle the A side. If cfg.device_can_rsp_on_same_cycle then we've actually done the
      // sampling already. Otherwise, we should check now.
      if (!cfg.device_can_rsp_on_same_cycle) begin
        a_chan_req_item = check_a_channel(.immediate(1'b0));
      end
      if (a_chan_req_item != null) begin
        a_chan_port.write(a_chan_req_item);
        if (cfg.synchronise_ports) channel_dir_port.write(AddrChannel);
        a_chan_req_item = null;
      end

      // We're done with this clock edge. If cfg.device_can_rsp_on_same_cycle, we now wait a short
      // time afterwards and sample a little after the clockedge.
      if (cfg.device_can_rsp_on_same_cycle) begin
        `DV_SPINWAIT_EXIT(
            #(cfg.time_a_valid_avail_after_sample_edge);,
            @(cfg.vif.mon_cb) `uvm_fatal(`gfn, $sformatf(
                "time_a_valid_avail_after_sample_edge (%0t) is over one cycle",
                cfg.time_a_valid_avail_after_sample_edge)))

        // It's a short time afterwards. Do the sampling!
        a_chan_req_item = check_a_channel(.immediate(1'b1));
        if (a_chan_req_item != null) begin
          a_chan_same_cycle_rsp_port.write(a_chan_req_item);
        end
      end
    end
  endtask

  // Check the A channel for a transaction
  //
  // If immediate is true, this is running just after a posedge of the clock, to allow us to capture
  // same-cycle responses. In this case, it samples the immediate values of the signals.
  //
  // Otherwise, this is running on the posedge. It samples signals through the mon_cb clocking
  // block.
  //
  // In either case, if a transaction is found then it returns a sequence item. Otherwise, it
  // returns null.
  function tl_seq_item check_a_channel(bit immediate);
    logic a_valid = immediate ? cfg.vif.h2d.a_valid : cfg.vif.mon_cb.h2d.a_valid;
    logic a_ready = immediate ? cfg.vif.d2h.a_ready : cfg.vif.mon_cb.d2h.a_ready;

    if (a_valid && a_ready) begin
      tl_seq_item req = tl_seq_item::type_id::create("req");
      tl_seq_item cloned_req;
      tlul_pkg::tl_h2d_t h2d = immediate ? cfg.vif.h2d : cfg.vif.mon_cb.h2d;

      // Create a sequence item. Note: this is a field in the class, which ad_channels_thread() uses
      // to pass the transaction to the relevant analysis port/ports.
      req.a_addr   = h2d.a_address;
      req.a_opcode = h2d.a_opcode;
      req.a_size   = h2d.a_size;
      req.a_param  = h2d.a_param;
      req.a_data   = h2d.a_data;
      req.a_mask   = h2d.a_mask;
      req.a_source = h2d.a_source;
      req.a_user   = h2d.a_user;
      `uvm_info("tl_logging",
                $sformatf("[%0s][a_chan] : %0s", agent_name, req.convert2string()),
                UVM_HIGH)

      if (cfg.en_cov) sample_outstanding_cov(req);

      `downcast(cloned_req, req.clone());
      `DV_CHECK_EQ_FATAL(cloned_req.a_source >> cfg.valid_a_source_width, 0)
      `DV_CHECK_EQ_FATAL(pending_a_req.exists(cloned_req.a_source), 0)
      pending_a_req[cloned_req.a_source] = cloned_req;

      if (cfg.max_outstanding_req > 0 && cfg.vif.rst_n === 1) begin
        if (pending_a_req.size() > cfg.max_outstanding_req) begin
          `uvm_error(`gfn,
                     $sformatf("Number of pending a_req exceeds limit %0d", pending_a_req.size()))
        end
        if (cfg.en_cov) cov.m_max_outstanding_cg.sample(pending_a_req.size());
      end
      return req;
    end

    return null;
  endfunction

  // Checks the D channel for a transaction
  //
  // If a transaction is found, writes it to d_chan_port and clears the corresponding pending
  // request.
  function void check_d_channel();
    if (cfg.vif.mon_cb.d2h.d_valid && cfg.vif.mon_cb.h2d.d_ready) begin
      tl_seq_item rsp;

      // A matching request must exist
      `DV_CHECK_FATAL(pending_a_req.exists(cfg.vif.mon_cb.d2h.d_source),
                      $sformatf("Cannot find request matching d_source 0x%0x",
                                cfg.vif.mon_cb.d2h.d_source))

      rsp = pending_a_req[cfg.vif.mon_cb.d2h.d_source];
      pending_a_req.delete(cfg.vif.mon_cb.d2h.d_source);

      rsp.d_opcode = cfg.vif.mon_cb.d2h.d_opcode;
      rsp.d_data   = cfg.vif.mon_cb.d2h.d_data;
      rsp.d_source = cfg.vif.mon_cb.d2h.d_source;
      rsp.d_param  = cfg.vif.mon_cb.d2h.d_param;
      rsp.d_error  = cfg.vif.mon_cb.d2h.d_error;
      rsp.d_sink   = cfg.vif.mon_cb.d2h.d_sink;
      rsp.d_size   = cfg.vif.mon_cb.d2h.d_size;
      rsp.d_user   = cfg.vif.mon_cb.d2h.d_user;

      `uvm_info("tl_logging",
                $sformatf("[%0s][d_chan] : %0s", agent_name, rsp.convert2string()), UVM_HIGH)

      d_chan_port.write(rsp);
      if (cfg.synchronise_ports) channel_dir_port.write(DataChannel);

      if (cfg.en_cov) cov.sample(rsp);
    end
  endfunction

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
