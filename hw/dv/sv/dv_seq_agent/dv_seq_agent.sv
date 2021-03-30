// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//
// An agent base class that wires up a dv_seq_monitor with outputs from a dv_seq_sequencer. This
// assumes that SEQUENCER_T is a subclass of dv_seq_sequencer, MONITOR_T is a subclass of
// dv_seq_monitor and that CFG_T is a subclass of dv_seq_agent_cfg.
//

class dv_seq_agent #(type CFG_T            = dv_seq_agent_cfg,
                     type DRIVER_T         = dv_base_driver,
                     type HOST_DRIVER_T    = DRIVER_T,
                     type DEVICE_DRIVER_T  = DRIVER_T,
                     type SEQUENCER_T      = dv_seq_sequencer,
                     type MONITOR_T        = dv_seq_monitor,
                     type COV_T            = dv_base_agent_cov)
  extends dv_base_agent #(.CFG_T           (CFG_T),
                          .DRIVER_T        (DRIVER_T),
                          .HOST_DRIVER_T   (HOST_DRIVER_T),
                          .DEVICE_DRIVER_T (DEVICE_DRIVER_T),
                          .SEQUENCER_T     (SEQUENCER_T),
                          .MONITOR_T       (MONITOR_T),
                          .COV_T           (COV_T));

  `uvm_component_param_utils(dv_seq_agent #(CFG_T, DRIVER_T, HOST_DRIVER_T, DEVICE_DRIVER_T,
                                            SEQUENCER_T, MONITOR_T, COV_T))
  `uvm_component_new

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    if (cfg.has_req_fifo) begin
      monitor.req_analysis_port.connect(sequencer.req_analysis_fifo.analysis_export);
    end
    if (cfg.has_rsp_fifo) begin
      monitor.rsp_analysis_port.connect(sequencer.rsp_analysis_fifo.analysis_export);
    end
  endfunction

endclass

