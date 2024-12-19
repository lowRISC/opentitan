// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Use this UVM macro as we may need to implement multiple uvm_analysis_imp, which means
// implemneting multiple write methods which is not possible with the same name.
`uvm_analysis_imp_decl(_agt_reset)

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

  // Analysis port only to forward the reset state to the sub-components to let them implement
  // their own write method from the uvm_analysis_imp according to their needs.
  uvm_analysis_export #(reset_state_e) reset_st_exp;

  uvm_analysis_imp_agt_reset #(reset_state_e, dv_base_agent#(CFG_T,DRIVER_T,HOST_DRIVER_T,
    DEVICE_DRIVER_T,SEQUENCER_T,MONITOR_T,COV_T)) reset_st_imp;

  function new (string name="", uvm_component parent=null);
    super.new(name, parent);
    reset_st_imp = new ("reset_st_imp", this);
  endfunction : new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // get CFG_T object from uvm_config_db
    if (!uvm_config_db#(CFG_T)::get(this, "", "cfg", cfg)) begin
      `uvm_fatal(`gfn, $sformatf("failed to get %s from uvm_config_db", cfg.get_type_name()))
    end
    `uvm_info(`gfn, $sformatf("\n%0s", cfg.sprint()), UVM_HIGH)

    if (cfg.has_reset) begin
      reset_st_exp = new("reset_st_exp", this);
    end

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

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    if (cfg.is_active && cfg.has_driver) begin
      driver.seq_item_port.connect(sequencer.seq_item_export);
    end
    // Manage connections to the reset analysis port
    if (cfg.has_reset) begin
      // To this agent
      reset_st_exp.connect(reset_st_imp);
      // To the driver
      if (cfg.has_driver) begin
        reset_st_exp.connect(driver.reset_st_imp);
      end
      // To the sequencer
      if (cfg.is_active) begin
        reset_st_exp.connect(sequencer.reset_st_imp);
      end
      // To the monitor
      reset_st_exp.connect(monitor.reset_st_imp);
    end
    if (cfg.has_req_fifo) begin
      monitor.req_analysis_port.connect(sequencer.req_analysis_fifo.analysis_export);
    end
    if (cfg.has_rsp_fifo) begin
      monitor.rsp_analysis_port.connect(sequencer.rsp_analysis_fifo.analysis_export);
    end
  endfunction

  virtual function void end_of_elaboration_phase(uvm_phase phase);
    super.end_of_elaboration_phase(phase);
    // Check if this agent reset state port has been connected, this info is only valid from
    // the end_of_elaboration phase. Do this check only if has_reset.
    if (cfg.has_reset && (reset_st_exp.size() < 1)) begin
      `uvm_fatal(`gfn, "Reset analysis port hasn't been connected to any reset agent")
    end
  endfunction : end_of_elaboration_phase

  virtual task run_phase(uvm_phase phase);
    // After each reset, the current transaction should be dropped and get_and_drive should be
    // restarted once the reset is being deasserted.
    forever begin
      // This isolation fork is needed to ensure that "disable fork" call won't kill any other
      // processes at the same level from the base classes
      fork begin : isolation_fork
        fork
          begin : main_thread
            run_main();
            wait(0);  // Wait indefinitely to ensure the fork will end because of a reset detection
          end
          begin : reset_thread
            if (cfg.has_reset) begin
              wait(cfg.in_reset);
            end else begin
              wait(0);
            end
          end
        join_any
        disable fork;   // Terminates all descendants and sub-descendants of isolation_fork
        wait(!cfg.in_reset);
      end join
    end
  endtask : run_phase

  virtual task run_main();
    // All the agents using the run_phase to run some things which should be restarted after each
    // reset operation, should overwrite this task as it will be called after reset detection.
  endtask : run_main

  // This function will be executed each time the reset monitor will detect a reset activity. As
  // the monitor will broadcast this activity on a UVM TLM port uvm_analysis_port which is connected
  // to this component via a UVM analysis import.
  virtual function void write_agt_reset(reset_state_e reset_st);
    // TODO MVy: use under_reset or cfg.in_reset ?
  endfunction : write_agt_reset

endclass
