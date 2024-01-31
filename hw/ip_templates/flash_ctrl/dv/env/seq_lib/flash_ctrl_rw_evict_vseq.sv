// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This test creates read buffer eviction by program_flash operation.
class flash_ctrl_rw_evict_vseq extends flash_ctrl_legacy_base_vseq;
  `uvm_object_utils(flash_ctrl_rw_evict_vseq)
  `uvm_object_new

  virtual task body();
    int page;
    int evict_trans, idx = 0;
    int evict_start = 0;

    rd_cache_t addr_q[$];

    flash_op_t init_ctrl;
    flash_dv_part_e part;

    // Enable interrupt for more visibility
    flash_ctrl_intr_enable(6'h3f);

    // Don't select a partition defined as read-only
    cfg.seq_cfg.avoid_ro_partitions = 1'b1;

    bank = $urandom_range(0, 1);

    fork
      begin
        rd_cache_t entry;

        while (idx < 50 && cfg.flash_ctrl_vif.fatal_err == 0) begin
          `DV_CHECK_RANDOMIZE_FATAL(this)
          rand_op.addr[OTFBankId] = bank;
          ctrl = rand_op;

          if (evict_start) begin
            addr_q.shuffle();
            entry = addr_q[0];
            ctrl.otf_addr = entry.addr;
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
                  int size, is_odd, tail;
                  is_odd = ctrl.addr[2];
                  size = (fractions + is_odd) / 2;
                  tail = (fractions + is_odd) % 2;
                  repeat (size) begin
                    addr_q.push_back(entry);
                    if (addr_q.size > 4) begin
                      rd_cache_t old_ent = addr_q.pop_front();
                    end
                    entry.addr += 8;
                  end
                  if (tail) begin
                    addr_q.push_back(entry);
                    if (addr_q.size > 4) begin
                      rd_cache_t old_ent = addr_q.pop_front();
                    end
                  end
                  readback_flash(ctrl, bank, 1, fractions);
                end
                3: begin
                  addr_q.push_back(entry);
                  if (addr_q.size > 4) begin
                    rd_cache_t old_ent = addr_q.pop_front();
                  end
                  direct_readback(ctrl.otf_addr, bank, 1);
                end
              endcase
            end else begin
              int size, is_odd, tail;
              is_odd = ctrl.addr[2];
              size = (fractions + is_odd) / 2;
              tail = (fractions + is_odd) % 2;
              repeat (size) begin
                addr_q.push_back(entry);
                if (addr_q.size > 4) begin
                  rd_cache_t old_ent = addr_q.pop_front();
                end
                entry.addr += 8;
              end
              if (tail) begin
                addr_q.push_back(entry);
                if (addr_q.size > 4) begin
                  rd_cache_t old_ent = addr_q.pop_front();
                end
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
  endtask

  virtual task send_evict(flash_op_t ctrl, int bank);
    prog_flash(ctrl, bank, 1, fractions);
  endtask // send_evict


endclass // flash_ctrl_rw_evict_vseq
