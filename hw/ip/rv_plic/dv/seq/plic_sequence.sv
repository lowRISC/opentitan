// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

class plic_sequence #(int src=32) extends uvm_sequence#(tl_seq_item);

  `uvm_object_utils(plic_sequence)

  uvm_tlm_analysis_fifo #(irq_seq_item#(src)) m_irq_fifo;

  function new(string name = "plic_sequence");
    super.new(name);
    m_irq_fifo = new("m_irq_fifo", null);
  endfunction : new

  virtual task body();
    automatic logic [31:0] base_addr;
    uvm_config_db#(logic [31:0])::get(null,"*","plic_base_address", base_addr);
    plic_init(base_addr);
  endtask : body

  task plic_init(logic [31:0] base_addr);
    // TODO: Configurable based on #Sources, #Targets, and interrupt type
    automatic int n_src, n_tgt, max_prio;
    automatic logic [31:0] rdata;
    automatic int src_reg_size;

    uvm_config_db#(int)::get(null,"*","num_source", n_src);
    uvm_config_db#(int)::get(null,"*","num_target", n_tgt);
    uvm_config_db#(int)::get(null,"*","max_priority", max_prio);


    src_reg_size = (n_src%32)? n_src/32 + 1: n_src/32;

    // Set Priority
    for (int i = 0 ; i < n_src ; i++) begin
      automatic logic [31:0] prio_addr;
      prio_addr = base_addr + rv_plic_reg_pkg::RV_PLIC_PRIO0_OFFSET ;
      tl_seq(prio_addr + (i<<2), 1'b1, $urandom_range(1, max_prio+1),rdata);
    end

    for (int i = 0 ; i < n_tgt ; i++) begin
      // set Threshold
      tl_seq(base_addr + rv_plic_reg_pkg::RV_PLIC_THRESHOLD0_OFFSET, 1'b1, 'h4, rdata);
    end

    // Int Source type
    for (int i = 0 ; i < src_reg_size ; i++) begin
      tl_seq(base_addr + ((src_reg_size + i)<<2), 1'b1, $urandom(), rdata);
    end

    // Int Enable
    for (int i = 0 ; i < src_reg_size ; i++) begin
      tl_seq(base_addr + rv_plic_reg_pkg::RV_PLIC_IE0_OFFSET +  (i<<2), 1'b1, '1, rdata);
    end
  endtask : plic_init

  task tl_seq(logic [31:0] address, logic write, logic [31:0] din, output logic [31:0] dout);
    req = tl_seq_item::type_id::create("req");
    rsp = tl_seq_item::type_id::create("rsp");
    start_item(req);
    req.addr = address;
    req.wr   = write;
    req.wdata = din;
    finish_item(req);
    get_response(rsp);
    dout = rsp.rdata;
  endtask : tl_seq

endclass : plic_sequence
