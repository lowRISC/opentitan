// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package flash_phy_prim_agent_pkg;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import dv_lib_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters

  // local types
  // forward declare classes to allow typedefs below
  typedef class flash_phy_prim_item;
  typedef class flash_phy_prim_agent_cfg;

  // reuse dv_base_sequencer as is with the right parameter set
  typedef dv_base_sequencer #(.ITEM_T(flash_phy_prim_item),
                              .CFG_T (flash_phy_prim_agent_cfg)) flash_phy_prim_sequencer;

  typedef logic [flash_phy_pkg::FullDataWidth-1:0] fdata_q_t[$];

  // functions

  function automatic void print_flash_data(fdata_q_t fq, string str = "fdata");
    `dv_info($sformatf(" flash data size: %0d",fq.size()), UVM_MEDIUM, str)
    foreach(fq[i]) begin
        `dv_info($sformatf("%4d:%2x_%1x_%8x_%8x", i,
                           fq[i][75:68], fq[i][67:64], fq[i][63:32], fq[i][31:0]),
                 UVM_MEDIUM, str)
    end
  endfunction

  // package sources
  `include "flash_phy_prim_item.sv"
  `include "flash_phy_prim_agent_cfg.sv"
  `include "flash_phy_prim_agent_cov.sv"
  `include "flash_phy_prim_driver.sv"
  `include "flash_phy_prim_monitor.sv"
  `include "flash_phy_prim_agent.sv"
  `include "flash_phy_prim_seq_list.sv"

endpackage: flash_phy_prim_agent_pkg
