// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class mbx_base_vseq extends cip_base_vseq #(
    .RAL_T               (mbx_core_reg_block),
    .CFG_T               (mbx_env_cfg),
    .COV_T               (mbx_env_cov),
    .VIRTUAL_SEQUENCER_T (mbx_virtual_sequencer)
  );

  bit do_mbx_init = 1'b1;
  mem_model seq_mem_model;
  rand bit [top_pkg::TL_AW-1:0] ibmbx_base_addr;
  rand bit [top_pkg::TL_AW-1:0] ibmbx_limit_addr;
  rand bit [top_pkg::TL_AW-1:0] obmbx_base_addr;
  rand bit [top_pkg::TL_AW-1:0] obmbx_limit_addr;

  mbx_mem_reg_block m_mbx_mem_ral;
  mbx_soc_reg_block m_mbx_soc_ral;

  `uvm_object_utils(mbx_base_vseq)

  constraint ib_ob_addr_range_c {
    (ibmbx_base_addr inside
      {[m_mbx_mem_ral.mem_ranges[0].start_addr : m_mbx_mem_ral.mem_ranges[0].end_addr]});
    (ibmbx_limit_addr inside
      {[m_mbx_mem_ral.mem_ranges[0].start_addr : m_mbx_mem_ral.mem_ranges[0].end_addr]});
    (obmbx_base_addr inside
      {[m_mbx_mem_ral.mem_ranges[0].start_addr : m_mbx_mem_ral.mem_ranges[0].end_addr]});
    (obmbx_limit_addr inside
      {[m_mbx_mem_ral.mem_ranges[0].start_addr : m_mbx_mem_ral.mem_ranges[0].end_addr]});
  }

  constraint legal_addr_range_c {
    (ibmbx_limit_addr > ibmbx_base_addr);
    ((obmbx_limit_addr - obmbx_base_addr) == (MBX_DV_DW_SIZE_BYTES * MBX_DV_MAX_DW));
  }

  constraint legal_non_overlapping_region_c {
    unique {ibmbx_base_addr, ibmbx_limit_addr, obmbx_base_addr, obmbx_limit_addr};
  }

  constraint legal_addr_alignment_c {
    (ibmbx_base_addr[1:0] == 0);
    (ibmbx_limit_addr[1:0] == 0);
    (obmbx_base_addr[1:0] == 0);
    (obmbx_limit_addr[1:0] == 0);
  }

  function new(string name = "");
    super.new();
    seq_mem_model = mem_model#()::type_id::create("seq_mem_model");
    seq_mem_model.init();
  endfunction: new

  function void pre_randomize();
    super.pre_randomize();
    `downcast(m_mbx_soc_ral, cfg.ral_models[cfg.mbx_soc_ral_name])
    `downcast(m_mbx_mem_ral, cfg.ral_models[cfg.mbx_mem_ral_name])
  endfunction: pre_randomize

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init();
    if (do_mbx_init == 1'b1) begin
      mbx_init();
    end
  endtask: dut_init

  virtual task start_device_seq();
    mbx_tl_device_seq seq_h;

    seq_h = mbx_tl_device_seq::type_id::create("seq_h");
    seq_h.mem = seq_mem_model;
    fork
      seq_h.start(p_sequencer.tl_sequencer_hs[cfg.mbx_mem_ral_name]);
    join_none
  endtask: start_device_seq

  virtual task write_mem(int start_addr, byte q[$]);
    `uvm_info(get_full_name(),
      $sformatf("write_mem(start_addr='h%0h, q=%p) -- Start", start_addr, q),
      UVM_DEBUG);
    foreach(q[ii]) begin
      seq_mem_model.write_byte((start_addr + ii), q[ii]);
    end
    `uvm_info(get_full_name(),
      $sformatf("write_mem(start_addr='h%0h, q=%p) -- End", start_addr, q),
      UVM_DEBUG);
  endtask: write_mem

  virtual task read_mem(int start_addr, int sz, ref byte q[$]);
    `uvm_info(get_full_name(),
      $sformatf("read_mem(start_addr='h%0h, sz=%0d) -- Start", start_addr, sz),
      UVM_DEBUG)
    q = {};
    for(int ii = 0; ii < sz; ii++) begin
      q[ii] = seq_mem_model.read_byte(start_addr + ii);
    end
    `uvm_info(get_full_name(),
      $sformatf("read_mem(start_addr='h%0h', sz=%0d, q=%p) -- Start", start_addr, sz, q),
      UVM_DEBUG)
  endtask: read_mem

  virtual task mbx_init();
    uvm_status_e status;

    `uvm_info(get_full_name(),
      $sformatf("mbx_init -- Start"),
      UVM_DEBUG)
    csr_wr(ral.inbound_base_address, ibmbx_base_addr);
    csr_wr(ral.inbound_limit_address, ibmbx_limit_addr);
    csr_wr(ral.outbound_base_address, obmbx_base_addr);
    csr_wr(ral.outbound_limit_address, obmbx_limit_addr);
    csr_wr(ral.outbound_object_size,  0);
    csr_wr(ral.control, 0);
    `uvm_info(get_full_name(),
      $sformatf("mbx_init -- End"),
      UVM_DEBUG)
  endtask: mbx_init

  virtual task wait_for_core_interrupt();
    `uvm_info(`gfn, $sformatf("wait_for_core_interrupt -- Start"), UVM_DEBUG)
    `DV_WAIT(cfg.intr_vif.pins == 1'b1)
    `uvm_info(`gfn, $sformatf("wait_for_core_interrupt -- End"), UVM_DEBUG)
  endtask: wait_for_core_interrupt

  virtual task body();
    `uvm_info(get_full_name(), "body -- Start", UVM_DEBUG)
    start_device_seq();
    `uvm_info(get_full_name(), "body -- End", UVM_DEBUG)
  endtask: body

endclass: mbx_base_vseq
