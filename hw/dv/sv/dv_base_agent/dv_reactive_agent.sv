// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// An extension of the base agent class that connects the monitor to the sequencer in order to allow
// the agent to run sequences that react to items collected by the monitor.
//
//   CFG_T:          The type of the configuration object. This should be a subclass of
//                   dv_reactive_agent_cfg
//
//   DRIVER_T:       The type of the driver. This should be a subclass of dv_base_driver.
//
//   HOST_DRIVER_T   The type of the driver when the agent configured with if_mode set to Host. This
//                   should be a subclass of DRIVER_T.
//
//   DEVICE_DRIVER_T The type of the driver when the agent configured with if_mode set to Device.
//                   This should be a subclass of DRIVER_T.
//
//   SEQUENCER_T     The type of the sequencer. This should be a subclass of dv_reactive_sequencer.
//
//   MONITOR_T       The type of the monitor. This should be a subclass of dv_reactive_monitor.
//
//   COV_T           The type of the object that monitors coverage. This should be a subclass of
//                   dv_base_agent_cov.

class dv_reactive_agent #(type CFG_T            = dv_reactive_agent_cfg,
                          type DRIVER_T         = dv_base_driver,
                          type HOST_DRIVER_T    = DRIVER_T,
                          type DEVICE_DRIVER_T  = DRIVER_T,
                          type SEQUENCER_T      = dv_reactive_sequencer,
                          type MONITOR_T        = dv_reactive_monitor,
                          type COV_T            = dv_base_agent_cov)
  extends dv_base_agent #(.CFG_T(CFG_T),
                          .DRIVER_T(DRIVER_T),
                          .HOST_DRIVER_T(HOST_DRIVER_T), .DEVICE_DRIVER_T(DEVICE_DRIVER_T),
                          .SEQUENCER_T(SEQUENCER_T),
                          .MONITOR_T(MONITOR_T),
                          .COV_T(COV_T));

  `uvm_component_param_utils(dv_reactive_agent #(CFG_T, DRIVER_T, HOST_DRIVER_T, DEVICE_DRIVER_T,
                                                 SEQUENCER_T, MONITOR_T, COV_T))

  extern function new (string name, uvm_component parent);
  extern function void connect_phase(uvm_phase phase);
endclass

function dv_reactive_agent::new (string name, uvm_component parent);
  super.new(name, parent);
endfunction

function void dv_reactive_agent::connect_phase(uvm_phase phase);
  super.connect_phase(phase);
  if (cfg.has_req_fifo) begin
    monitor.req_analysis_port.connect(sequencer.req_analysis_fifo.analysis_export);
  end
  if (cfg.has_rsp_fifo) begin
    monitor.rsp_analysis_port.connect(sequencer.rsp_analysis_fifo.analysis_export);
  end
endfunction
