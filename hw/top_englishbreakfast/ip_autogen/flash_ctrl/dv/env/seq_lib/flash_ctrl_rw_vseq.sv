// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Generates random mix of reads and writes. Writes are somewhat delicate: when scrambling or ECC
// are enabled we can only write full flash words (8 bytes), so the number of bus words needs to
// be even and the starting address needs to be 8-byte aligned. This is ensured by the consraints.
//
// In addition, overwrites will almost surely cause ecc errors to be injected because bits cannot
// flip from 0 to 1, so this makes sure addresses don't overlap previously written ones.
class flash_ctrl_rw_vseq extends flash_ctrl_otf_base_vseq;
  `uvm_object_utils(flash_ctrl_rw_vseq)
  `uvm_object_new

  flash_op_t ctrl;
  int num, bank;

  virtual task body();
    bit prev_addr_flash_word_aligned = cfg.seq_cfg.addr_flash_word_aligned;
    bit prev_avoid_ro_partitions = cfg.seq_cfg.avoid_ro_partitions;

    cfg.clk_rst_vif.wait_clks(5);
    fork
      begin
        repeat(cfg.otf_num_rw) begin
          randcase
            cfg.otf_wr_pct: begin
              `DV_CHECK(try_create_prog_op(ctrl, bank, num), "Could not create a prog flash op")
              prog_flash(ctrl, bank, num, fractions);
            end
            cfg.otf_rd_pct: begin
              set_ecc_err_target(TgtRd);
              `DV_CHECK_RANDOMIZE_FATAL(this)
              ctrl = rand_op;
              get_bank_and_num(ctrl, bank, num);
              read_flash(ctrl, bank, num, fractions);
            end
          endcase
        end
      end
      begin
        launch_host_rd();
      end
    join
  endtask : body

  virtual task launch_host_rd();
    for (int i = 0; i < cfg.otf_num_hr; ++i) begin
      fork
        send_rand_host_rd();
      join_none
      #0;
    end
    csr_utils_pkg::wait_no_outstanding_access();
  endtask : launch_host_rd
endclass : flash_ctrl_rw_vseq
