// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class flash_otf_item extends uvm_object;
  `uvm_object_utils(flash_otf_item)
  flash_op_t cmd;
  data_q_t   dq;
  fdata_q_t  raw_fq, fq;
  function new(string name = "flash_otf_item");
    super.new(name);
  endfunction // new

  virtual function void print(string name = "flash_otf_item");
    `dv_info($sformatf("partition : %s", cmd.partition.name()), UVM_MEDIUM, name)
    `dv_info($sformatf("erase_type: %s", cmd.erase_type.name()), UVM_MEDIUM, name)
    `dv_info($sformatf("op        : %s", cmd.op.name()), UVM_MEDIUM, name)
    `dv_info($sformatf("prog_sel  : %s", cmd.prog_sel.name()), UVM_MEDIUM, name)
    `dv_info($sformatf("num_words : %0d", cmd.num_words), UVM_MEDIUM, name)
    `dv_info($sformatf("s_addr    : 0x%x", cmd.addr), UVM_MEDIUM, name)
    flash_otf_print_data64(dq, name);
  endfunction // do_print

  function void get_wd_from_phy(flash_phy_prim_item item);
    // dv has 3 Infos while rtl has 1.
    // TODO: align below routine with both dv and rtl data struct.
    this.cmd.partition = flash_dv_part_e'(item.req.part);
    if (item.req.pg_erase_req) this.cmd.erase_type = FlashErasePage;
    if (item.req.bk_erase_req) this.cmd.erase_type = FlashEraseBank;
    this.cmd.op = FlashOpProgram;
    this.cmd.prog_sel = flash_prog_sel_e'(item.req.prog_type);
    this.cmd.num_words = item.fq.size() * 2;
    this.cmd.addr = item.req.addr;

    fq = item.fq;
  endfunction // get_from_phy

  // Layout:
  // bit: 63..32, 31..0
  // fq = dq[1] , dq[0];
  function fdata_q_t dq2fq(data_q_t dq);
    logic [flash_phy_pkg::FullDataWidth-1:0] fdata;
    int                                      size = dq.size() / 2;
    for (int i = 0 ; i < size; ++i) begin
      fdata = 'h0;
      fdata[top_pkg::TL_DW-1:0] = dq.pop_front();
      fdata[top_pkg::TL_DW*2-1:top_pkg::TL_DW] = dq.pop_front();
      dq2fq.push_back(fdata);
    end

    // if wq size is odd number,
    // push remainer to upper half of fdata.
    if (dq.size() > 0) begin
      fdata = 'h0;
      fdata[top_pkg::TL_DW-1:0] = dq.pop_front();
      dq2fq.push_back(fdata);
    end
  endfunction // dq2fq

  function void scramble(bit[flash_phy_pkg::KeySize-1:0] addr_key,
                         bit[flash_phy_pkg::KeySize-1:0] data_key,
                         bit[flash_ctrl_pkg::BusAddrW-1:0] addr);
    raw_fq = dq2fq(this.dq);
    if (raw_fq.size == 0) begin
      `uvm_error(`gfn, "raw_fq is empty")
      return;
    end

    `uvm_info(`gfn, $sformatf("wr_enc:size:%0d addr:%x  akey:%x  dkey:%x",raw_fq.size(),
                              addr, addr_key, data_key), UVM_MEDIUM)
    foreach (raw_fq[i]) begin
      fq.push_back(create_flash_data(raw_fq[i], addr, addr_key, data_key));
      addr += 8;
    end
  endfunction
endclass // flash_otf_item
