// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
class rjtag_driver extends uvm_driver #(rjtag_seq_item);

  // JTAG Interface
  virtual jtag_if vif;

  `uvm_component_utils(rjtag_driver)

  //uvm_analysis_port #(rjtag_seq_item) rjtag_port;

  function new (string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(virtual jtag_if)::get(this,"","vif",vif)) begin
      `uvm_fatal("NO_VIF", {"virtual interface must be set for:",
        get_full_name(),".vif"});
    end
  endfunction : build_phase

  // run phase
  virtual task run_phase(uvm_phase phase);
    // Initialize RISC-V Debug Module
    //   DMActive
    vif.tms = 1'b0;
    wait(vif.trst_n == 1'b1);
    repeat(10) @(negedge vif.tck);

    forever begin
      seq_item_port.get_next_item(req);
      //respond_to_transfer(req);
      drive();
      seq_item_port.item_done();
    end
  endtask : run_phase

  virtual task drive();
    req.print();
    if (req.dmi_wr == 1'b1) dmi_wr(req);
    else                    dmi_rd(req);
  endtask : drive

  task dmi_wr(rjtag_seq_item req);
    jtag_wr(5, 5'h11, 41, {req.dmi_addr, req.dmi_wdata, 2'h2} );
  endtask : dmi_wr

  task dmi_rd(rjtag_seq_item req);
    automatic bit [63:0] dout;
    jtag_shift(5, 5'h11, 41, {req.dmi_addr, req.dmi_wdata, 2'h1}, dout);
    jtag_shift(5, 5'h11, 41, {req.dmi_addr, req.dmi_wdata, 2'h0}, dout);
    //$cast(rsp, req.clone());
    //rsp.dmi_rdata = dout[33:2];
    req.dmi_rdata = dout[33:2];
  endtask : dmi_rd

  task jtag_wr( int alen, bit [4:0] addr, int dlen, bit [63:0] data);
    automatic bit [63:0] dout;
    jtag_shift(alen, addr, dlen, data, dout);
  endtask : jtag_wr

  task jtag_shift(int alen, bit [4:0] addr, int dlen, bit [63:0] din, bit [63:0] dout);
    jtag_shift_ir(alen, addr);
    jtag_shift_dr(dlen, din, dout);
  endtask : jtag_shift

  task jtag_shift_ir( int alen, bit [4:0] addr);
    // Assume starting in RTI state
                        vif.tms = 1'b1; vif.tdi = 1'b0; // SelectDR
    @(negedge vif.tck); vif.tms = 1'b1; vif.tdi = 1'b0; // SelectIR
    @(negedge vif.tck); vif.tms = 1'b0; vif.tdi = 1'b0; // CaptureIR
    @(negedge vif.tck); vif.tms = 1'b0; vif.tdi = 1'b0; // ShiftIR
    for(int i=0; i < alen; i++) begin
      @(negedge vif.tck);
      vif.tms = (i == alen-1) ? 1'b1 : 1'b0; // to Exit1IR if end of addr.
      vif.tdi = addr[i];
    end
    @(negedge vif.tck); vif.tms = 1'b1; vif.tdi = 1'b0; // UpdateIR
    @(negedge vif.tck); vif.tms = 1'b0; vif.tdi = 1'b0; // RTI
    @(negedge vif.tck);
  endtask : jtag_shift_ir

  task jtag_shift_dr ( int dlen, logic [63:0] data, logic [63:0] dout);
    // assume starting in RTI
                          vif.tms = 1'b1; vif.tdi = 1'b0; // go to SelectDR
    @(negedge vif.tck);   vif.tms = 1'b0; vif.tdi = 1'b0; // go to CaptureDR
    @(negedge vif.tck);   vif.tms = 1'b0; vif.tdi = 1'b0; // go to ShiftDR
    for(int i=0;i<dlen-1;i++) begin
      @(negedge vif.tck); vif.tms = 1'b0; vif.tdi = data[i];// stay in ShiftDR
      @(posedge vif.tck); dout[i] = vif.tdo;
    end
    @(negedge vif.tck);   vif.tms = 1'b1; vif.tdi = data[dlen-1];// go to Exit1DR
    @(posedge vif.tck);   dout[dlen-1] = vif.tdo;
    @(negedge vif.tck);   vif.tms = 1'b1; vif.tdi = 1'b0; // go to UpdateIR
    @(negedge vif.tck);   vif.tms = 1'b0; vif.tdi = 1'b0; // go to RTI

    @(negedge vif.tck);
  endtask


endclass
