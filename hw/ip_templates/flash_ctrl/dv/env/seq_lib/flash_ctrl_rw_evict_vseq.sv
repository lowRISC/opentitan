// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This test creates read buffer eviction by program_flash operation,
// careful not to reuse evict addresses since they would cause a
// double write, leading to integrity errors. This means the items in
// addr_q are always popped, and addr_q needs to be replenished.
class flash_ctrl_rw_evict_vseq extends flash_ctrl_legacy_base_vseq;
  `uvm_object_utils(flash_ctrl_rw_evict_vseq)
  `uvm_object_new

  // We keep up to this many items in addr_q.
  parameter int TargetAddrQSize = 4;

  // This holds the collection of addresses that are candidates for eviction.
  rd_cache_t addr_q[$];

  local function void add_to_addr_q(rd_cache_t entry);
    addr_q.push_back(entry);
    if (addr_q.size > TargetAddrQSize) begin
      rd_cache_t old_ent = addr_q.pop_front();
    end
  endfunction

  virtual task body();
    int page;
    int evict_trans, idx = 0;
    int evict_start = 0;

    flash_op_t init_ctrl;
    flash_dv_part_e part;

    // Enable interrupt for more visibility
    flash_ctrl_intr_enable(6'h3f);

    bank = $urandom_range(0, 1);

    fork
      begin
        rd_cache_t entry;

        while (idx < 50 && cfg.flash_ctrl_vif.fatal_err == 0) begin
          int num;
          `DV_CHECK(try_create_prog_op(ctrl, bank, num), "Could not create a prog flash op")
          ctrl.num_words = fractions;
          if (evict_start && addr_q.size >= TargetAddrQSize) begin
            addr_q.shuffle();
            entry = addr_q.pop_front();
            ctrl.addr = entry.addr;
            ctrl.otf_addr = entry.addr;
            `uvm_info(`gfn, $sformatf(
                      "The address to evict is 0x%x, chosen from %p", entry.addr, addr_q),
                      UVM_MEDIUM)
            ctrl.partition = entry.part;
            init_ctrl = ctrl;
            send_evict(ctrl, bank);
            ctrl = init_ctrl;
            if (ctrl.partition == FlashPartData) begin
              randcase
                1: readback_flash(ctrl, bank, 1, fractions);
                1: direct_readback(ctrl.otf_addr, bank, 1);
              endcase
            end else begin
              readback_flash(ctrl, bank, 1, fractions);
            end

          end else begin
            entry.bank = bank;
            entry.addr = ctrl.otf_addr;
            entry.part = ctrl.partition;

            if (ctrl.partition == FlashPartData) begin
              randcase
                1: begin
                  int size;
                  `DV_CHECK(!ctrl.addr[2], "Unexpected addr[2] set")
                  size = fractions  / 2;
                  repeat (size) begin
                    add_to_addr_q(entry);
                    entry.addr += 8;
                  end
                  readback_flash(ctrl, bank, 1, fractions);
                end
                3: begin
                  add_to_addr_q(entry);
                  direct_readback(ctrl.otf_addr, bank, 1);
                end
              endcase
            end else begin
              int size;
              size = fractions / 2;
              `DV_CHECK(!ctrl.addr[2] && !fractions[0], "Odd address or fractions")
              repeat (size) begin
                add_to_addr_q(entry);
                entry.addr += 8;
              end
              readback_flash(ctrl, bank, 1, fractions);
            end
            `uvm_info("seq", $sformatf("idx:%0d done",idx), UVM_HIGH)
          end // else: !if(evct_start)
          idx++;
        end // while (idx < 30 && cfg.flash_ctrl_vif.fatal_err == 0)
        `uvm_info("seq",
                  $sformatf("read complete fatal:%0d", cfg.flash_ctrl_vif.fatal_err), UVM_HIGH)
      end // fork begin
      begin
        time timeout_ns = 100_000_000;
        evict_trans = $urandom_range(10, 20);
        `uvm_info("seq", $sformatf("wait evict start %0d", evict_trans), UVM_MEDIUM)
        `DV_SPINWAIT( wait(idx == evict_trans);,
                      $sformatf("Timed out waiting for evict trans %0d idx:%0d",
                                evict_trans, idx), timeout_ns,
                      "seq")
        evict_start = 1;
      end
    join
    cfg.seq_cfg.disable_flash_init = 1;
  endtask : body

  // We evict two bus words (one flash word).
  virtual task send_evict(flash_op_t ctrl, int bank);
    prog_flash(ctrl, bank, /*num=*/1, /*wd=*/2);
  endtask : send_evict

endclass : flash_ctrl_rw_evict_vseq
