// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Miscellaneous class to maintain read address
class flash_otf_read_entry extends uvm_object;
  `uvm_object_utils(flash_otf_read_entry)
  string name;
  rd_cache_t prv_read[NumBanks][$];
  bit hash[rd_cache_t];
  `uvm_object_new

  // Push to prv_read.
  // When size > 4, pop the oldest entry
  function void insert(rd_cache_t it, flash_op_t flash_op);
    rd_cache_t ot;
    int        size, is_odd, tail;
    addr_t aligned_addr;
    is_odd = flash_op.addr[2];
    size = (flash_op.num_words + is_odd) / 2;
    tail = (flash_op.num_words + is_odd) % 2;
    aligned_addr = it.addr;
    aligned_addr[2:0] = 'h0;

    for (int i = 0; i < size; i++) begin
      it.addr = aligned_addr;
      if (!hash.exists(it)) begin
        prv_read[it.bank].push_back(it);
        hash[it] = 1;
        if (prv_read[it.bank].size > 4) begin
          ot = prv_read[it.bank].pop_front();
          hash.delete(ot);
        end
      end
      aligned_addr += 8;
    end // for (int i = 0; i < size; i++)
    if (tail) begin
      it.addr = aligned_addr;
      if (!hash.exists(it)) begin
        prv_read[it.bank].push_back(it);
        hash[it] = 1;
        if (prv_read[it.bank].size > 4) begin
          ot = prv_read[it.bank].pop_front();
          hash.delete(ot);
        end
      end
    end
  endfunction

  // Check whether a given flash_op has any overlap on
  // read cache.
  function bit check(rd_cache_t it, flash_op_t flash_op);
    int        size, is_odd, tail;
    addr_t aligned_addr;
    is_odd = flash_op.addr[2];
    size = (flash_op.num_words + is_odd) / 2;
    tail = (flash_op.num_words + is_odd) % 2;
    aligned_addr = it.addr;
    aligned_addr[2:0] = 'h0;

    for (int i = 0; i < size; i++) begin
      it.addr = aligned_addr;
      if (hash.exists(it)) return 1;
      aligned_addr += 8;
    end // for (int i = 0; i < size; i++)
    if (tail) begin
      it.addr = aligned_addr;
      if (hash.exists(it)) return 1;
    end
    return 0;
  endfunction // check

  // Update hash for program, erase operation
  function void update(rd_cache_t it, flash_op_t flash_op);
    rd_cache_t d_ent[$];
    if (flash_op.op == FlashOpErase) begin
      if (flash_op.erase_type == FlashErasePage) begin
        // Collect entries which is the same as erase page number.
        int epage = addr2page({it.bank, it.addr});
        foreach (hash[ent]) begin
          if (addr2page({ent.bank, ent.addr}) == epage) d_ent.push_back(ent);
        end
      end else begin
        // Collect entries which is the same erase bank id.
        foreach (hash[ent]) begin
          if (ent.bank == it.bank) d_ent.push_back(ent);
        end
      end
    end else if (flash_op.op == FlashOpProgram) begin
      int        size, is_odd, tail;
      addr_t aligned_addr;
      is_odd = flash_op.addr[2];
      size = (flash_op.num_words + is_odd) / 2;
      tail = (flash_op.num_words + is_odd) % 2;
      aligned_addr = it.addr;
      aligned_addr[2:0] = 'h0;
      // Collect all write word collide with read cache
      for (int i = 0; i < size; i++) begin
        it.addr = aligned_addr;
        if (hash.exists(it)) begin
          d_ent.push_back(it);
        end
      end
      if (tail) begin
        it.addr = aligned_addr;
        if (hash.exists(it)) begin
          d_ent.push_back(it);
        end
      end
    end
    while (d_ent.size() > 0) begin
      rd_cache_t my_ent = d_ent.pop_front();
      rd_cache_t cp_ent_q[$] = prv_read[my_ent.bank];
      prv_read[my_ent.bank] = {};

      hash.delete(my_ent);
      for (int i = 0; i < cp_ent_q.size(); i++) begin
        if (cp_ent_q[i] != my_ent) prv_read[my_ent.bank].push_back(cp_ent_q[i]);
      end
    end
  endfunction

  function int addr2page(bit[OTFBankId:0] addr);
    return (int'(addr[OTFBankId:11]));
  endfunction // addr2page

  function void print(string str = "flash_otf_read_entry");
    for(int i = 0; i < NumBanks; ++i) begin
      foreach (prv_read[i][j]) begin
        `uvm_info(str, $sformatf("ent[%0d][%0d]: %p", i, j, prv_read[i][j]), UVM_MEDIUM)
      end
    end
  endfunction // print
endclass // flash_otf_read_entry
