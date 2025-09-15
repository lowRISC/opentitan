// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Random read write with access resolution of 1 word (4byte).
class flash_ctrl_rw_rnd_wd_vseq extends flash_ctrl_otf_base_vseq;
  `uvm_object_utils(flash_ctrl_rw_rnd_wd_vseq)
  `uvm_object_new

  constraint ctrl_data_num_c {ctrl_num inside {[1:32]};}
  constraint fractions_c {
    solve ctrl_num before fractions;
    if (ctrl_num == 1)
      fractions dist { [1:4] := 4, [5:16] := 1};
    else
      fractions == 16;
  }

  constraint odd_addr_c {
    solve fractions before is_addr_odd;
    (fractions == 16) -> is_addr_odd == 0;
  }

  virtual task body();
    flash_op_t ctrl;
    int num, bank;

    cfg.clk_rst_vif.wait_clks(5);

    fork
      begin
        repeat(500) begin
          bit is_prog = 0;
          randcase
            cfg.otf_wr_pct: begin
              `DV_CHECK(try_create_prog_op(ctrl, bank, num), "Could not create a prog flash op")
              is_prog = 1;
            end
            1: begin
              `DV_CHECK_RANDOMIZE_FATAL(this)
              get_bank_and_num(ctrl, bank, num);
            end
          endcase
          if (is_prog) prog_flash(ctrl, bank, num, fractions);
          else read_flash(ctrl, bank, num, fractions);
        end
      end
      begin
         for (int i = 0; i < 100; ++i) begin
            fork
              send_rand_host_rd();
            join_none
            #0;
         end
         csr_utils_pkg::wait_no_outstanding_access();
      end
    join
  endtask
endclass : flash_ctrl_rw_rnd_wd_vseq
