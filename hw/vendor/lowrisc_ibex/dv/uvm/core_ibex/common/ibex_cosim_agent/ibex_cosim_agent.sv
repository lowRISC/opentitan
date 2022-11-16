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

  function void write_mem_word(bit [31:0] addr, bit [DATA_WIDTH-1:0] d);
    for (int i = 0; i < DATA_WIDTH / 8; i++) begin
      write_mem_byte(addr + i, d[7:0]);
      d = d >> 8;
    end
  endfunction

  // Backdoor-load the test binary file into the cosim memory model
  function void load_binary_to_mem(bit[31:0] base_addr, string bin);
     bit [7:0]   r8;
     bit [31:0]  addr = base_addr;
     int         bin_fd;
    bin_fd = $fopen(bin,"rb");
    if (!bin_fd)
      `uvm_fatal(get_full_name(), $sformatf("Cannot open file %0s", bin))
    while ($fread(r8,bin_fd)) begin
      `uvm_info(`gfn, $sformatf("Init mem [0x%h] = 0x%0h", addr, r8), UVM_FULL)
      write_mem_byte(addr, r8);
      addr++;
    end
  endfunction

  function void reset();
    scoreboard.rvfi_port.flush();
    scoreboard.dmem_port.flush();
    scoreboard.imem_port.flush();
    scoreboard.ifetch_port.flush();
    scoreboard.ifetch_pmp_port.flush();

    scoreboard.reset_e.trigger();
  endfunction : reset

endclass : ibex_cosim_agent
