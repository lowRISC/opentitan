// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

package tl_agent_pkg;
  // dep packages
  import uvm_pkg::*;
  import top_pkg::*;
  import tlul_pkg::*;
  import mem_model_pkg::*;
  import dv_lib_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  parameter int AddrWidth   = top_pkg::TL_AW;
  parameter int DataWidth   = top_pkg::TL_DW;
  parameter int SizeWidth   = top_pkg::TL_SZW;
  parameter int MaskWidth   = top_pkg::TL_DBW;
  parameter int SourceWidth = top_pkg::TL_AIW;
  parameter int DUserWidth  = top_pkg::TL_DUW;
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
  `include "tl_seq_lib.sv"
  `include "tl_monitor.sv"
  `include "tl_agent.sv"
  `include "tl_reg_adapter.sv"

endpackage
