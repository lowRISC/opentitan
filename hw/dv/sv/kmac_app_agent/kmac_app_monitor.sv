// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class kmac_app_monitor extends dv_base_monitor #(
    .ITEM_T (kmac_app_item),
    .CFG_T  (kmac_app_agent_cfg),
    .COV_T  (kmac_app_agent_cov)
  );
  `uvm_component_utils(kmac_app_monitor)

  // the base class provides the following handles for use:
  // kmac_app_agent_cfg: cfg
  // kmac_app_agent_cov: cov
  // uvm_analysis_port #(kmac_app_item): analysis_port

  uvm_tlm_analysis_fifo#(push_pull_item#(`CONNECT_DATA_WIDTH)) data_fifo;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    data_fifo = new("data_fifo", this);
  endfunction

  virtual protected task collect_trans(uvm_phase phase);
    forever fork
      begin : isolation_fork
        fork
          process_trans();
          @(negedge cfg.vif.rst_n);
        join_any
        disable fork;
        process_reset();
      end : isolation_fork
    join
  endtask

  // collect transactions forever - already forked in dv_base_moditor::run_phase
  virtual protected task process_trans();
    forever begin
      kmac_app_item req = kmac_app_item::type_id::create("req");
      kmac_app_item rsp;

      while (1) begin
        bit [KmacDataIfWidth-1:0] data;
        bit [KmacDataIfWidth/8-1:0] strb;
        bit last;
        push_pull_item#(`CONNECT_DATA_WIDTH) data_item;

        // KMAC (device) supports prematurely ending an App transaction and going back to Idle state
        // before the full data has been sent from the connected App host (KeyMgr/ROM/LC).
        // As a result, we need to set `ok_to_end` here otherwise the monitor's corresponding
        // objection will never drop in this scenario.
        // TODO, we can consider to handle premature ending better. Once sequence ends transaction
        // prematurely, issue a reset to get out of this while-loop, so that we can keep
        // ok_to_end = 0 for the entire transaction.
        ok_to_end = 1;
        data_fifo.get(data_item);
        {data, strb, last} = data_item.h_data;

        for (int i = 0; i < KmacDataIfWidth/8; i++) begin
          if (strb[i]) req.byte_data_q.push_back(data[i*8+:8]);
        end

        if (last) begin
          ok_to_end = 0;
          break;
        end
      end
      req_analysis_port.write(req);
      `uvm_info(`gfn, $sformatf("Write req item:\n%0s", req.sprint()), UVM_HIGH)

      `downcast(rsp, req.clone())
      while (cfg.vif.rsp_done !== 1) @(cfg.vif.mon_cb);
      rsp.rsp_error         = cfg.vif.rsp_error;
      rsp.rsp_digest_share0 = cfg.vif.rsp_digest_share0;
      rsp.rsp_digest_share1 = cfg.vif.rsp_digest_share1;
      analysis_port.write(rsp);
      `uvm_info(`gfn, $sformatf("Write rsp item:\n%0s", rsp.sprint()), UVM_HIGH)
      ok_to_end = 1;
    end
  endtask

  virtual protected task process_reset();
    `uvm_info(`gfn, $sformatf("Reset occurs"), UVM_MEDIUM)
    ok_to_end = 1;
    @(posedge cfg.vif.rst_n);
    data_fifo.flush();
  endtask

endclass
