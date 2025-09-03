// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A base agent class
//
//   CFG_T:          The type of the configuration object. This should be a subclass of
//                   dv_base_agent_cfg
//
//   DRIVER_T:       The type of the driver. This should be a subclass of dv_base_driver.
//
//   HOST_DRIVER_T   The type of the driver when the agent configured with if_mode set to Host. This
//                   should be a subclass of DRIVER_T.
//
//   DEVICE_DRIVER_T The type of the driver when the agent configured with if_mode set to Device.
//                   This should be a subclass of DRIVER_T.
//
//   SEQUENCER_T     The type of the sequencer. This should be a subclass of dv_base_sequencer.
//
//   MONITOR_T       The type of the monitor. This should be a subclass of dv_base_monitor.
//
//   COV_T           The type of the object that monitors coverage. This should be a subclass of
//                   dv_base_agent_cov.

class dv_base_agent #(type CFG_T            = dv_base_agent_cfg,
                      type DRIVER_T         = dv_base_driver,
                      type HOST_DRIVER_T    = DRIVER_T,
                      type DEVICE_DRIVER_T  = DRIVER_T,
                      type SEQUENCER_T      = dv_base_sequencer,
                      type MONITOR_T        = dv_base_monitor,
                      type COV_T            = dv_base_agent_cov) extends uvm_agent;

  `uvm_component_param_utils(dv_base_agent #(CFG_T, DRIVER_T, HOST_DRIVER_T, DEVICE_DRIVER_T,
                                             SEQUENCER_T, MONITOR_T, COV_T))

  CFG_T       cfg;
  COV_T       cov;
  DRIVER_T    driver;
  SEQUENCER_T sequencer;
  MONITOR_T   monitor;

  extern function new (string name="", uvm_component parent=null);

  extern function void build_phase(uvm_phase phase);
  extern function void connect_phase(uvm_phase phase);
endclass

function dv_base_agent::new (string name="", uvm_component parent=null);
  super.new(name, parent);
endfunction

function void dv_base_agent::build_phase(uvm_phase phase);
  super.build_phase(phase);
  // get CFG_T object from uvm_config_db
  if (!uvm_config_db#(CFG_T)::get(this, "", "cfg", cfg)) begin
    `uvm_fatal(`gfn, $sformatf("failed to get %s from uvm_config_db", cfg.get_type_name()))
  end
  `uvm_info(`gfn, $sformatf("\n%0s", cfg.sprint()), UVM_HIGH)

  // create components
  if (cfg.en_cov) begin
    cov = COV_T ::type_id::create("cov", this);
    cov.cfg = cfg;
  end

  monitor = MONITOR_T::type_id::create("monitor", this);
  monitor.cfg = cfg;
  monitor.cov = cov;

  if (cfg.is_active) begin
    sequencer = SEQUENCER_T::type_id::create("sequencer", this);
    sequencer.cfg = cfg;

    if (cfg.has_driver) begin
      if (cfg.if_mode == Host)  driver = HOST_DRIVER_T::type_id::create("driver", this);
      else                      driver = DEVICE_DRIVER_T::type_id::create("driver", this);
      driver.cfg = cfg;
    end
  end
endfunction

function void dv_base_agent::connect_phase(uvm_phase phase);
  super.connect_phase(phase);
  if (cfg.is_active && cfg.has_driver) begin
    driver.seq_item_port.connect(sequencer.seq_item_export);
  end
  if (cfg.has_req_fifo) begin
    monitor.req_analysis_port.connect(sequencer.req_analysis_fifo.analysis_export);
  end
  if (cfg.has_rsp_fifo) begin
    monitor.rsp_analysis_port.connect(sequencer.rsp_analysis_fifo.analysis_export);
  end
endfunction
