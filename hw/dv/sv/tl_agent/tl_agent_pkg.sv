// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

package tl_agent_pkg;
  // dep packages
  import uvm_pkg::*;
  import bus_params_pkg::*;
  import tlul_pkg::*;
  import mem_model_pkg::*;
  import dv_lib_pkg::*;
  import dv_base_reg_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  parameter int AddrWidth   = bus_params_pkg::BUS_AW;
  parameter int DataWidth   = bus_params_pkg::BUS_DW;
  parameter int SizeWidth   = bus_params_pkg::BUS_SZW;
  parameter int MaskWidth   = bus_params_pkg::BUS_DBW;
  parameter int SourceWidth = bus_params_pkg::BUS_AIW;
  parameter int AUserWidth  = bus_params_pkg::BUS_AUW;
  parameter int DUserWidth  = bus_params_pkg::BUS_DUW;
  parameter int OpcodeWidth = 3;

  typedef class tl_seq_item;
  typedef class tl_agent_cfg;
  // reuse dv_base_driver as is with the right parameter set
  typedef dv_base_driver #(tl_seq_item, tl_agent_cfg) tl_base_driver;

  // TileLink conformance level
  typedef enum bit [1:0] {
    kTLUL,
    kTLUH,
    kTLC
  } tl_level_e;

  typedef enum {
    AddrChannel,
    DataChannel
  } tl_channels_e;

  function automatic void enable_logging(string file_name="tl_agent.log");
    int log_fd = $fopen(file_name,"w");
    `uvm_info("tl_agent_pkg", $sformatf("The TL agent transaction log will be saved to %0s",
                              file_name), UVM_LOW)
    uvm_top.set_report_id_verbosity_hier("tl_logging", UVM_HIGH);
    uvm_top.set_report_id_file_hier("tl_logging", log_fd);
    uvm_top.set_report_id_verbosity_hier("tl_logging", UVM_HIGH);
    // Always save in a separate log file and disable printing on the screen
    uvm_top.set_report_severity_id_action_hier(UVM_INFO, "tl_logging", UVM_LOG);
    uvm_top.set_report_severity_id_action_hier(UVM_WARNING,
                                               "tl_logging", UVM_DISPLAY | UVM_LOG);
    uvm_top.set_report_severity_id_action_hier(UVM_ERROR,
                                               "tl_logging", UVM_DISPLAY | UVM_LOG | UVM_COUNT);
    uvm_top.set_report_severity_id_action_hier(UVM_FATAL,
                                               "tl_logging", UVM_DISPLAY | UVM_LOG | UVM_EXIT);
  endfunction

  `include "tl_seq_item.sv"
  `include "tl_agent_cfg.sv"
  `include "tl_agent_cov.sv"
  `include "tl_host_driver.sv"
  `include "tl_device_driver.sv"
  `include "tl_sequencer.sv"
  `include "tl_monitor.sv"
  `include "tl_agent.sv"
  `include "tl_reg_adapter.sv"
  `include "tl_seq_list.sv"

endpackage
