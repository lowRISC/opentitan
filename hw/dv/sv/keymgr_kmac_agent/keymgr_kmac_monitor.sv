// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class keymgr_kmac_monitor extends dv_base_monitor #(
    .ITEM_T (keymgr_kmac_item),
    .CFG_T  (keymgr_kmac_agent_cfg),
    .COV_T  (keymgr_kmac_agent_cov)
  );
  `uvm_component_utils(keymgr_kmac_monitor)

  // the base class provides the following handles for use:
  // keymgr_kmac_agent_cfg: cfg
  // keymgr_kmac_agent_cov: cov
  // uvm_analysis_port #(keymgr_kmac_item): analysis_port

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
      keymgr_kmac_item req = keymgr_kmac_item::type_id::create("req");
      keymgr_kmac_item rsp;

      while (1) begin
        bit [KmacDataIfWidth-1:0] data;
        bit [KmacDataIfWidth/8-1:0] strb;
        bit last;
        push_pull_item#(`CONNECT_DATA_WIDTH) data_item;

        data_fifo.get(data_item);
        {data, strb, last} = data_item.h_data;
        ok_to_end = 0;

        while (strb > 0) begin
          if (strb[0]) req.byte_data_q.push_back(data[7:0]);
          data = data >> 8;
          strb = strb >> 1;
        end
        if (last) break;
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
