// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class csrng_monitor extends dv_base_monitor #(
    .ITEM_T (csrng_item),
    .CFG_T  (csrng_agent_cfg),
    .COV_T  (csrng_agent_cov)
  );
  `uvm_component_utils(csrng_monitor)

  // the base class provides the following handles for use:
  // csrng_agent_cfg: cfg
  // csrng_agent_cov: cov
  // uvm_analysis_port #(csrng_item): analysis_port

  // item will be sent to this port when req phase is done (last is set)
  uvm_analysis_port#(csrng_item) req_port;
  // item will be sent to this port when rsp phase is done (rsp_done is set)
  uvm_analysis_port#(csrng_item) rsp_port;

  `uvm_component_new
  bit in_reset;

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    req_port  = new("req_port", this);
    rsp_port  = new("rsp_port", this);
  endfunction

  task run_phase(uvm_phase phase);
    @(posedge cfg.vif.rst_n);
    fork
      handle_reset();
      // TODO: implement function
      // collect_valid_trans();
      // We only need to monitor incoming requests if the agent is configured
      // in device mode.
      if (cfg.if_mode == dv_utils_pkg::Device) begin
        collect_request();
      end
    join_none
  endtask

  virtual protected task handle_reset();
    forever begin
      @(negedge cfg.vif.rst_n);
      in_reset = 1;
      // TODO: sample any reset-related covergroups
      @(posedge cfg.vif.rst_n);
      in_reset = 0;
    end
  endtask

  // This task is only used for device agents responding
  // It will pick up any incoming requests from the DUT and send a signal to the
  // sequencer (in the form of a sequence item), which will then be forwarded to
  // the sequence, which then generates the appropriate response item.
  //
  // TODO: This assumes no requests can be dropped, and might need to be fixed
  //       if this is not allowed.
  virtual protected task collect_request();
    csrng_item   item;
    forever begin
      @(cfg.vif.req_push_if.mon_cb);
      if (cfg.vif.req_push_if.mon_cb.valid) begin
        // TODO: sample any covergroups
	// TODO: Implement suggestion in PR #5456
        item = csrng_item::type_id::create("item");
        item.acmd = cfg.vif.mon_cb.cmd_req.csrng_req_bus[3:0];
        `uvm_info(`gfn, $sformatf("Captured item: %s", item.convert2string()), UVM_HIGH)
        req_port.write(item);
        // After picking up a request, wait until a response is sent before
        // detecting another request, as this is not a pipelined protocol.
        `DV_SPINWAIT_EXIT(while (!cfg.vif.mon_cb.cmd_rsp.csrng_rsp_ack) @(cfg.vif.mon_cb);,
                          wait(in_reset))
       end
    end
  endtask

  // TODO: collect_trans

endclass
