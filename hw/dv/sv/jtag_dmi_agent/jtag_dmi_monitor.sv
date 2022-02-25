// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class jtag_dmi_monitor extends dv_base_monitor #(.ITEM_T(jtag_dmi_item));
  `uvm_component_utils(jtag_dmi_monitor)

  uvm_tlm_analysis_fifo #(jtag_item) jtag_item_fifo;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    jtag_item_fifo = new("jtag_item_fifo", this);
  endfunction

  virtual protected task collect_trans(uvm_phase phase);
    // TODO.
  endtask

endclass
