// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class flash_otf_item extends uvm_object;
  `uvm_object_utils(flash_otf_item)
  flash_op_t cmd;
  data_q_t   dq;
  fdata_q_t  raw_fq, fq;
  bit[flash_ctrl_pkg::BusAddrByteW-1:0] start_addr;
  bit[flash_phy_pkg::KeySize-1:0]      addr_key, data_key;
  bit [flash_ctrl_pkg::BusAddrByteW-2:0] mem_addr;
  bit                                    head_pad, tail_pad;
  bit                                    scr_en, ecc_en;
  int                                    page;
  flash_mp_region_cfg_t region;
  flash_mp_region_cfg_t ctrl_rd_region_q[$];

  bit                                    derr;
  // other expected error than double bit ecc
  bit                                    exp_err;

  bit                                    skip_err_chk;
  addr_t                                 err_addr, eaddr_q[$];
  function new(string name = "flash_otf_item");
    super.new(name);
    head_pad = 0;
    tail_pad = 0;
    derr = 0;
    exp_err = 0;
    skip_err_chk = 0;
  endfunction // new

  virtual function void print(string name = "flash_otf_item");
    `dv_info($sformatf("partition : %s", cmd.partition.name()), UVM_MEDIUM, name)
    `dv_info($sformatf("erase_type: %s", cmd.erase_type.name()), UVM_MEDIUM, name)
    `dv_info($sformatf("op        : %s", cmd.op.name()), UVM_MEDIUM, name)
    `dv_info($sformatf("prog_sel  : %s", cmd.prog_sel.name()), UVM_MEDIUM, name)
    `dv_info($sformatf("num_words : %0d", cmd.num_words), UVM_MEDIUM, name)
    `dv_info($sformatf("s_addr    : 0x%x", start_addr), UVM_MEDIUM, name)
    `dv_info($sformatf("mem_addr  : 0x%x", mem_addr), UVM_MEDIUM, name)

    if (dq.size() > 0) begin
      flash_otf_print_data64(dq, name);
    end else begin // read
      printfq(fq, name);
    end
  endfunction // do_print

  function void printfq(fdata_q_t fq, string name = "printfq");
    foreach (fq[i]) begin
      `dv_info($sformatf("rdata%0d: %8x_%8x", i, fq[i][63:32], fq[i][31:0]), UVM_MEDIUM, name)
    end
  endfunction

  function void get_from_phy(flash_phy_prim_item item, string rw);
    this.cmd.partition = flash_dv_part_e'(item.req.part);
    if (item.req.pg_erase_req) this.cmd.erase_type = FlashErasePage;
    if (item.req.bk_erase_req) this.cmd.erase_type = FlashEraseBank;
    if (rw == "w") begin
      this.cmd.op = FlashOpProgram;
      this.cmd.num_words = item.fq.size() * 2;
    end else begin
      this.cmd.op = FlashOpRead;
      this.cmd.num_words = 1;
    end
    this.cmd.prog_sel = flash_prog_sel_e'(item.req.prog_type);
    this.cmd.addr = item.req.addr;
    // cmd.addr can be modified to call bkdr mem access
    // So we need to exptra copy of mem interface address
    this.mem_addr = item.req.addr;
    fq = item.fq;
  endfunction // get_from_phy

  // Layout:
  // bit: 75...64 | 63..32, 31..0
  // fq =  0s...  | dq[1] , dq[0];
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

  // Inverse of dq2fq, copy fq to dq.
  function data_q_t fq2dq(fdata_q_t fq);
    int size = fq.size();

    for (int i = 0; i < size; ++i) begin
      fq2dq.push_back(fq[i][31:0]);
      fq2dq.push_back(fq[i][63:32]);
    end
  endfunction

  // Scramble dq data and store result to fq.
  // Use 'create_flash_data' function from package
  function void scramble(bit [flash_phy_pkg::KeySize-1:0] addr_key,
                         bit [flash_phy_pkg::KeySize-1:0] data_key,
                         bit [flash_ctrl_pkg::BusAddrByteW-2:0] addr,
                         bit dis = 1,
                         bit add_icv_err = 0);
    bit [FlashDataWidth-1:0] data;
    bit [71:0]               data_with_icv;
    bit [75:0]               ecc_76;

    if (region == null) begin
      `uvm_fatal("scramble", "region should be assigned before calling this function")
    end else begin
      scr_en = (region.scramble_en == MuBi4True);
      ecc_en = (region.ecc_en == MuBi4True);
    end

   raw_fq = dq2fq(this.dq);
    if (raw_fq.size == 0) begin
      `uvm_error(`gfn, "raw_fq is empty")
      return;
    end
    if (dis) begin
    `uvm_info("wr_scr", $sformatf("size:%0d addr:%x  akey:%x  dkey:%x scr_en:%0d ecc_en:%0d",
                              raw_fq.size(), addr, addr_key, data_key, scr_en, ecc_en), UVM_MEDIUM)
    end
    foreach(raw_fq[i]) begin
      data = raw_fq[i][FlashDataWidth-1:0];
      if (ecc_en) begin
        data_with_icv = prim_secded_pkg::prim_secded_hamming_72_64_enc(raw_fq[i][63:0]);
        if (add_icv_err) begin
          data_with_icv[67:64] = ~data_with_icv[67:64];
        end
      end else begin
        // We only need bit 67:64 when ecc_en == true.
        // So set all vector to zero when ecc_en is off.
        data_with_icv = 'h0;
      end

      if (scr_en) begin
        data = create_flash_data(raw_fq[i], addr, addr_key, data_key, dis);
      end
      if (ecc_en) begin
        fq.push_back(
           prim_secded_pkg::prim_secded_hamming_76_68_enc({data_with_icv[67:64], data[63:0]}));
      end else begin
        fq.push_back({12'h0, data});
      end
      addr += 8;
    end
  endfunction // scramble

  // Descramble fq data and store result to fq and dq.
  // Use 'create_raw_data' function from package
  function void descramble(bit[flash_phy_pkg::KeySize-1:0] addr_key,
                           bit[flash_phy_pkg::KeySize-1:0] data_key);
    bit ecc_err, icv_err;
    prim_secded_pkg::secded_hamming_76_68_t dec68;
    bit [flash_phy_pkg::FullDataWidth-1:0] data; // 76 bits
    bit [71:0]               data_with_icv;
    bit[flash_ctrl_pkg::BusAddrByteW-2:0] addr = mem_addr;
    data_q_t   tmp_dq;

    ecc_err = 'h0;
    if (region == null && ctrl_rd_region_q.size == 0) begin
      `uvm_fatal("descramble", "region should be assigned before calling this function")
    end else if (ctrl_rd_region_q.size == 0) begin
      scr_en = (region.scramble_en == MuBi4True);
      ecc_en = (region.ecc_en == MuBi4True);
      `uvm_info("rd_scr", $sformatf("size:%0d addr:%x scr_en:%0d ecc_en:%0d",
                                    fq.size(), addr, scr_en, ecc_en), UVM_MEDIUM)
    end else begin
      if (fq.size != ctrl_rd_region_q.size) begin
        `uvm_fatal("descramble", $sformatf({"fq:%0d != region_q:%0d",
                                            " region q should be the same size as read data"},
                                           fq.size, ctrl_rd_region_q.size))
      end
    end
    foreach (fq[i]) begin
       // erase data skip descramble
      if (fq[i] == {flash_phy_pkg::FullDataWidth{1'b1}}) begin
         raw_fq.push_back(fq[i]);
      end else begin
        if (ctrl_rd_region_q.size > 0) begin
          scr_en = (ctrl_rd_region_q[i].scramble_en == MuBi4True);
          ecc_en = (ctrl_rd_region_q[i].ecc_en == MuBi4True);
          `uvm_info("rd_scr", $sformatf("size:%0d idx:%0d addr:%x scr_en:%0d ecc_en:%0d",
                                        fq.size(), i, addr, scr_en, ecc_en), UVM_MEDIUM)
        end
        if (ecc_en) begin
          dec68 = prim_secded_pkg::prim_secded_hamming_76_68_dec(fq[i]);
        end else begin
          dec68.data = fq[i][67:0];
        end

        if (scr_en) begin
          data = create_raw_data(dec68.data[63:0], addr, addr_key, data_key);
          data[67:64] = dec68.data[67:64];
        end else begin
          data = dec68.data;
        end

        // check ecc
        // chec icv
        if (ecc_en) begin
          data_with_icv = prim_secded_pkg::prim_secded_hamming_72_64_enc(data[63:0]);
          icv_err = (data_with_icv[67:64] != data[67:64]);
          ecc_err |= (dec68.err[1] | icv_err);
          if (dec68.err[1] | icv_err) begin
            err_addr = addr << 3;
            eaddr_q.push_back(err_addr);
            `uvm_info("DCR_DBG", $sformatf("%4d:err_addr:%x err76:%2b synd:%x icv_err:%2b",
                                           i, err_addr, dec68.err, dec68.syndrome, icv_err),
                      UVM_MEDIUM)
          end
          if (dec68.err[0]) begin
            `uvm_info("SERR_DBG", $sformatf("%4d: serr:%1b data:%x -- > %x",
                                            i, dec68.err[0], fq[i], dec68.data), UVM_MEDIUM)
          end
        end

        raw_fq.push_back(data);

        if (skip_err_chk == 0 && ecc_err != 0) begin
          `uvm_error("rd_scr", "ecc error is detected")
        end
      end
      addr++;
    end
    // collect upto cmd.num_words
    tmp_dq = fq2dq(raw_fq);
    dq = '{};
    for (int i = 0; i < cmd.num_words; i++) begin
      dq.push_back(tmp_dq[i]);
    end
    if (head_pad) dq = dq[1:$];
    if (tail_pad) dq = dq[0:$-1];
    raw_fq = dq2fq(dq);
    derr = ecc_err;
  endfunction // descramble

  function void clear_qs();
    this.dq = '{};
    this.raw_fq = '{};
    this.fq = '{};
  endfunction // clear_qs
endclass // flash_otf_item
