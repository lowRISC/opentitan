// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Random read write with access resolution of 1 word (4byte).
class flash_ctrl_rw_rnd_wd_vseq extends flash_ctrl_otf_base_vseq;
  `uvm_object_utils(flash_ctrl_rw_rnd_wd_vseq)
  `uvm_object_new

  constraint ctrl_num_c { ctrl_num dist { CtrlTransMin := 7, [2:31] :/ 1, CtrlTransMax := 2}; }
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
          `DV_CHECK_RANDOMIZE_FATAL(this)
          ctrl = rand_op;
          bank = rand_op.addr[OTFBankId];
          if (ctrl.partition == FlashPartData) begin
            num = $urandom_range(1, 32);
          end else begin
            num = $urandom_range(1, InfoTypeSize[rand_op.partition >> 1]);
            // Max transfer size of info is 512Byte.
            if (num * fractions > 128) begin
              num = 128 / fractions;
            end
          end
          // If the partition that selected configured as read-only, skip the program
          sync_otf_wr_ro_part();
          randcase
            cfg.otf_wr_pct:prog_flash(ctrl, bank, num, fractions);
            1:read_flash(ctrl, bank, num, fractions);
          endcase
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
endclass // flash_ctrl_rw_rnd_wd_vseq
