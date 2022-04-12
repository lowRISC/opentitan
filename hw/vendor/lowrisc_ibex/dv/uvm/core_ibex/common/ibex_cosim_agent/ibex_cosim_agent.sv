// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "cosim_dpi.svh"

class ibex_cosim_agent extends uvm_agent;
  ibex_rvfi_monitor rvfi_monitor;
  ibex_ifetch_monitor ifetch_monitor;
  ibex_ifetch_pmp_monitor ifetch_pmp_monitor;
  ibex_cosim_scoreboard scoreboard;

  uvm_analysis_export#(ibex_mem_intf_seq_item) dmem_port;
  uvm_analysis_export#(ibex_mem_intf_seq_item) imem_port;

  `uvm_component_utils(ibex_cosim_agent)

  function new(string name="", uvm_component parent=null);
    super.new(name, parent);

    dmem_port = new("dmem_port", this);
    imem_port = new("imem_port", this);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    rvfi_monitor       = ibex_rvfi_monitor::type_id::create("rvfi_monitor", this);
    scoreboard         = ibex_cosim_scoreboard::type_id::create("scoreboard", this);
    ifetch_monitor     = ibex_ifetch_monitor::type_id::create("ifetch_monitor", this);
    ifetch_pmp_monitor = ibex_ifetch_pmp_monitor::type_id::create("ifetch_pmp_monitor", this);
  endfunction: build_phase

  virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);

    rvfi_monitor.item_collected_port.connect(scoreboard.rvfi_port.analysis_export);
    ifetch_monitor.item_collected_port.connect(scoreboard.ifetch_port.analysis_export);
    ifetch_pmp_monitor.item_collected_port.connect(scoreboard.ifetch_pmp_port.analysis_export);
    dmem_port.connect(scoreboard.dmem_port.analysis_export);
    imem_port.connect(scoreboard.imem_port.analysis_export);
  endfunction: connect_phase

  function void write_mem_byte(bit [31:0] addr, bit [7:0] d);
    riscv_cosim_write_mem_byte(scoreboard.cosim_handle, addr, d);
  endfunction
endclass : ibex_cosim_agent
