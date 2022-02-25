// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package jtag_dmi_agent_pkg;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import dv_base_reg_pkg::*;
  import csr_utils_pkg::*;
  import dv_lib_pkg::*;
  import jtag_agent_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // local types
  // JTAG DMI op driven by the JTAG host.
  typedef enum logic [1:0] {
    DmiOpNone = 0,
    DmiOpRead = 1,
    DmiOpWrite = 2
  } jtag_dmi_op_req_e;

  // JTAG DMI op status read back by the JTAG host.
  typedef enum logic [1:0] {
    DmiOpOk = 0,
    DmiOpFailed = 2,
    DmiOpInProgress = 3
  } jtag_dmi_op_rsp_e;

  // Represents the JTAG DMI op field, either driver or monitored, as a union.
  typedef union packed {
    jtag_dmi_op_req_e op_req;
    jtag_dmi_op_rsp_e op_rsp;
  } jtag_dmi_op_t;

  // package sources
  `include "jtag_dmi_reg_block.sv"
  `include "jtag_dmi_reg_frontdoor.sv"
  `include "jtag_dmi_item.sv"
  `include "jtag_dmi_monitor.sv"

  // Convenience function to create JTAG DMI RAL block.
  function automatic jtag_dmi_reg_block create_jtag_dmi_reg_block(jtag_agent_cfg cfg);
    jtag_dmi_reg_block jtag_dmi_ral = jtag_dmi_reg_block::type_id::create("jtag_dmi_ral");
    jtag_dmi_ral.build(.base_addr(0), .csr_excl(null));
    jtag_dmi_ral.set_support_byte_enable(1'b0);
    jtag_dmi_ral.lock_model();
    jtag_dmi_ral.compute_mapped_addr_ranges();
    jtag_dmi_ral.compute_unmapped_addr_ranges();
    // TODO: fix the computation of mapped and unmapped ranges.

    // Attach JTAG DMI frontdoor to all registers.
    begin
      uvm_reg rg[$];
      semaphore sem = new(1);
      jtag_dmi_ral.get_registers(rg);
      foreach (rg[i]) begin
        jtag_dmi_reg_frontdoor ftdr = jtag_dmi_reg_frontdoor::type_id::create("ftdr");
        ftdr.jtag_agent_cfg_h = cfg;
        ftdr.jtag_dtm_ral_sem_h = sem;
        rg[i].set_frontdoor(ftdr);
      end
    end
    return jtag_dmi_ral;
  endfunction

endpackage: jtag_dmi_agent_pkg
