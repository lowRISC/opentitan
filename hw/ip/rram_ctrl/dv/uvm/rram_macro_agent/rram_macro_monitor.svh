// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Monitor that reports transactions between rram_ctrl and rram_macro
//
// Note that ok_to_end tracking is done in collect_trans and collect_between_resets, rather than in
// a monitor_ready_to_end task (as expected by dv_base_monitor). This makes it easier to link to
// tracking "open requests", which collect_between_resets is already handling.

class rram_macro_monitor extends dv_base_monitor #(.ITEM_T (rram_macro_rsp_seq_item),
                                                   .CFG_T (rram_macro_agent_cfg));
  `uvm_component_utils(rram_macro_monitor)

  extern function new(string name, uvm_component parent);

  // Collect transactions forever. This implements a task from dv_base_monitor.
  extern virtual protected task collect_trans();

  // Collect requests and responses, writing pairs to the analysis port. Will be killed if reset is
  // asserted.
  extern local task collect_between_resets();
endclass

function rram_macro_monitor::new(string name, uvm_component parent);
  super.new(name, parent);
endfunction

task rram_macro_monitor::collect_trans();
  wait(!$isunknown(cfg.m_vif.rst_ni));
  cfg.in_reset = !cfg.m_vif.rst_ni;
  forever begin
    wait (cfg.m_vif.rst_ni);
    cfg.in_reset = 0;
    fork : isolation_fork begin
      fork
        wait (!cfg.m_vif.rst_ni);
        collect_between_resets();
      join_any
      disable fork;
    end join

    cfg.in_reset = 1;
    ok_to_end = 1;
  end
endtask

task rram_macro_monitor::collect_between_resets();
  rram_macro_req_seq_item req;

  forever begin
    // Wait for a request to be acked (visible by rd_req or wr_req being true and the ack being
    // true) or for a response to be sent (visible by done being true).
    @(cfg.m_vif.mon_cb iff
      (((cfg.m_vif.mon_cb.req.rd_req || cfg.m_vif.mon_cb.req.wr_req) && cfg.m_vif.mon_cb.rsp.ack) ||
       cfg.m_vif.mon_cb.rsp.done));

    // Is a response available?
    if (cfg.m_vif.mon_cb.rsp.done) begin
      if (req == null) begin
        // The macro shouldn't send responses without a request in flight.
        `uvm_error("stray_rsp", "Unexpected response from macro with no request in flight.")
      end else begin
        rram_macro_rsp_seq_item rsp = rram_macro_rsp_seq_item::type_id::create("rsp");

        rsp.m_err       = cfg.m_vif.mon_cb.rsp.err;
        rsp.m_ecc_err   = cfg.m_vif.mon_cb.rsp.ecc_err;
        rsp.m_rd_data   = cfg.m_vif.mon_cb.rsp.rd_data;
        rsp.m_init_done = cfg.m_vif.mon_cb.rsp.init_done;
        rsp.m_fatal_err = cfg.m_vif.mon_cb.rsp.fatal_err;
        rsp.m_recov_err = cfg.m_vif.mon_cb.rsp.recov_err;
        rsp.m_req       = req;

        // This is split explicitly into read and write transactions so that they can be reported
        // with different IDs (allowing filtering with +uvm_set_verbosity)
        if (rsp.m_req.m_wr_req) begin
          `uvm_info("wr_txn",
                    $sformatf("Seen macro write transaction:\n%0s", rsp.sprint()),
                    UVM_HIGH)
        end
        if (rsp.m_req.m_rd_req) begin
          `uvm_info("rd_txn",
                    $sformatf("Seen macro read transaction:\n%0s", rsp.sprint()),
                    UVM_HIGH)
        end

        analysis_port.write(rsp);

        req = null;
      end
    end

    // Is a request being acked?
    if ((cfg.m_vif.mon_cb.req.rd_req || cfg.m_vif.mon_cb.req.wr_req) &&
        cfg.m_vif.mon_cb.rsp.ack) begin
      // If so, there had better not already be a request waiting for a response (not something that
      // the protocol supports)
      if (req != null) begin
        `uvm_error("extra_ack", "Unexpected ack from macro when there was a request in flight.")
      end else begin
        req = rram_macro_req_seq_item::type_id::create("req");
        req.m_rd_req  = cfg.m_vif.mon_cb.req.rd_req;
        req.m_wr_req  = cfg.m_vif.mon_cb.req.wr_req;
        req.m_wr_last = cfg.m_vif.mon_cb.req.wr_last;
        req.m_addr    = cfg.m_vif.mon_cb.req.addr;
        req.m_wr_data = cfg.m_vif.mon_cb.req.wr_data;
        req.m_part    = cfg.m_vif.mon_cb.req.part;
        req.m_ecc_en  = cfg.m_vif.mon_cb.req.ecc_en;
      end
    end

    ok_to_end = (req == null);
  end
endtask
