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

  // The maximum number of attempts to get an address that has not been previously written.
  localparam int MaxProgAttempts = 16;

  flash_op_t ctrl;
  int num, bank;

  constraint fractions_c {
    fractions[0] == 0;
    fractions > 1;
    fractions <= 16;
  }

  function void get_bank_and_num(input flash_op_t rand_op, ref int bank, ref int num);
    bank = rand_op.addr[OTFBankId];
    num = rand_op.partition == FlashPartData ? ctrl_num : ctrl_info_num;
  endfunction

  // Randomizes until a flash operation satisfies the constraints and its address has not
  // previously written. It issues an error when failing.
  protected function bit try_create_prog_op();
    int attempts = 0;

    while (attempts < MaxProgAttempts) begin
      otf_addr_t end_addr;

      // Add constraints to avoid half-word writes and to avoid readonly
      // partitions.
      `DV_CHECK_RANDOMIZE_FATAL(this)
      ctrl = rand_op;
      ctrl.num_words = fractions;
      get_bank_and_num(ctrl, bank, num);
      end_addr = ctrl.otf_addr + (num * fractions * 4) - 1;
      if (!address_range_was_written(to_full_addr(ctrl.otf_addr, bank),
                                     to_full_addr(end_addr, bank))) begin
        return 1'b1;
      end
      ++attempts;
    end
    `DV_CHECK(0, "Too many unsuccessful attempts to create a prog_op")
    return 1'b0;
  endfunction : try_create_prog_op

  virtual task body();
    bit prev_addr_flash_word_aligned = cfg.seq_cfg.addr_flash_word_aligned;
    bit prev_avoid_ro_partitions = cfg.seq_cfg.avoid_ro_partitions;

    cfg.clk_rst_vif.wait_clks(5);
    fork
      begin
        repeat(cfg.otf_num_rw) begin
          randcase
            cfg.otf_wr_pct: begin
              cfg.seq_cfg.addr_flash_word_aligned = 1'b1;
              cfg.seq_cfg.avoid_ro_partitions = 1'b1;
              `DV_CHECK(try_create_prog_op(), "Could not create a prog flash op")
              prog_flash(ctrl, bank, num, fractions);
              cfg.seq_cfg.addr_flash_word_aligned = prev_addr_flash_word_aligned;
              cfg.seq_cfg.avoid_ro_partitions = prev_avoid_ro_partitions;
            end
            cfg.otf_rd_pct: begin
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
