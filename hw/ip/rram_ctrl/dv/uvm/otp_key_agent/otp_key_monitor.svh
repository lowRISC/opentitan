// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Monitor that spots key transactions on otp_key_if
//
// Note that ok_to_end tracking is done in collect_trans and collect_between_resets, rather than in
// a monitor_ready_to_end task (as expected by dv_base_monitor). This makes it easier to link to
// tracking "open requests", which collect_between_resets is already handling.


class otp_key_monitor extends dv_base_monitor #(.ITEM_T (otp_key_rsp_seq_item),
                                                .CFG_T (otp_key_agent_cfg));
  `uvm_component_utils(otp_key_monitor)

  extern function new (string name, uvm_component parent);

  // Collect transactions forever. This implements a task from dv_base_monitor.
  extern virtual protected task collect_trans();

  // Collect requests and responses, writing pairs to the analysis port. Will be killed if reset is
  // asserted.
  extern local task collect_between_resets();
endclass

function otp_key_monitor::new (string name, uvm_component parent);
  super.new(name, parent);
endfunction

task otp_key_monitor::collect_trans();
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

task otp_key_monitor::collect_between_resets();
  otp_key_req_seq_item data_req, addr_req;

  forever begin
    // Wait for a new addr/data request (visible because the addr_req or data_req signal will be
    // true when we don't have an item representing it) or an ack on either side.
    @(cfg.m_vif.mon_cb iff
      ((cfg.m_vif.mon_cb.req.data_req && (data_req == null)) ||
       (cfg.m_vif.mon_cb.req.addr_req && (addr_req == null)) ||
       cfg.m_vif.mon_cb.rsp.data_ack ||
       cfg.m_vif.mon_cb.rsp.addr_ack));

    if (cfg.m_vif.mon_cb.req.data_req && (data_req == null)) begin
      data_req = otp_key_req_seq_item::type_id::create("data_req");
      data_req.m_is_data_req = 1'b1;
    end

    if (cfg.m_vif.mon_cb.req.addr_req && (addr_req == null)) begin
      addr_req = otp_key_req_seq_item::type_id::create("addr_req");
      addr_req.m_is_data_req = 1'b0;
    end

    if (cfg.m_vif.mon_cb.rsp.data_ack) begin
      if (data_req == null) begin
        `uvm_error("extra_data_ack", "No request for data ack.")
      end else begin
        otp_key_rsp_seq_item rsp = otp_key_rsp_seq_item::type_id::create("rsp");

        rsp.m_key        = cfg.m_vif.mon_cb.rsp.key;
        rsp.m_rand_key   = cfg.m_vif.mon_cb.rsp.rand_key;
        rsp.m_seed_valid = cfg.m_vif.mon_cb.rsp.seed_valid;
        rsp.m_req        = data_req;
        analysis_port.write(rsp);

        data_req = null;
      end
    end

    if (cfg.m_vif.mon_cb.rsp.addr_ack) begin
      if (addr_req == null) begin
        `uvm_error("extra_addr_ack", "No request for addr ack.")
      end else begin
        otp_key_rsp_seq_item rsp = otp_key_rsp_seq_item::type_id::create("rsp");

        rsp.m_key        = cfg.m_vif.mon_cb.rsp.key;
        rsp.m_rand_key   = cfg.m_vif.mon_cb.rsp.rand_key;
        rsp.m_seed_valid = cfg.m_vif.mon_cb.rsp.seed_valid;
        rsp.m_req        = addr_req;
        analysis_port.write(rsp);

        addr_req = null;
      end
    end

    ok_to_end = (data_req == null) && (addr_req == null);

    @(cfg.m_vif.mon_cb);
  end
endtask
