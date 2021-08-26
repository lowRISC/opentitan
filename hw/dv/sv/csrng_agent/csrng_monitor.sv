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

  uvm_tlm_analysis_fifo#(push_pull_item#(.HostDataWidth(csrng_pkg::CSRNG_CMD_WIDTH)))
      csrng_cmd_fifo;

  bit in_reset;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    csrng_cmd_fifo = new("csrng_cmd_fifo", this);
  endfunction

  task run_phase(uvm_phase phase);
    @(posedge cfg.vif.rst_n);
    fork
      handle_reset();
      collect_valid_trans();
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

  virtual task collect_valid_trans();
    push_pull_item#(.HostDataWidth(csrng_pkg::CSRNG_CMD_WIDTH))  item;
    csrng_item   cs_item;

    cs_item = csrng_item::type_id::create("cs_item");

    forever begin
      for (int i = 0; i <= cs_item.clen; i++) begin
        csrng_cmd_fifo.get(item);
	if (i == 0) begin
          cs_item.acmd  = item.h_data[3:0];
          cs_item.clen  = item.h_data[7:4];
          cs_item.flags = item.h_data[11:8];
          cs_item.glen  = item.h_data[30:12];
          cs_item.cmd_data_q.delete();
        end
        else begin
          cs_item.cmd_data_q.push_back(item.h_data);
        end
      end
      `uvm_info(`gfn, $sformatf("Captured item: %s", cs_item.convert2string()), UVM_HIGH)
      analysis_port.write(cs_item);
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
      @(cfg.vif.cmd_push_if.mon_cb);
      if (cfg.vif.cmd_push_if.mon_cb.valid) begin
        // TODO: sample any covergroups
	// TODO: Implement suggestion in PR #5456
        item = csrng_item::type_id::create("item");
        item.acmd = cfg.vif.mon_cb.cmd_req.csrng_req_bus[3:0];
        `uvm_info(`gfn, $sformatf("Captured item: %s", item.convert2string()), UVM_HIGH)
        req_analysis_port.write(item);
        // After picking up a request, wait until a response is sent before
        // detecting another request, as this is not a pipelined protocol.
        `DV_SPINWAIT_EXIT(while (!cfg.vif.mon_cb.cmd_rsp.csrng_rsp_ack) @(cfg.vif.mon_cb);,
                          wait(in_reset))
       end
    end
  endtask
endclass
