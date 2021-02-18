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

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    req_port  = new("req_port", this);
    rsp_port  = new("rsp_port", this);
  endfunction

  task run_phase(uvm_phase phase);
//    super.run_phase(phase);
  endtask

  // TODO: collect_trans

endclass
