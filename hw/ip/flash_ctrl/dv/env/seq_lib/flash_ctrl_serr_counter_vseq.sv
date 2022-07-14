// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Directed test to check flash_ctrl.single_err_cnt
// Use low error injection pct to avoid counter saturation.
// Counter can be saturated but not all the time.
class flash_ctrl_serr_counter_vseq extends flash_ctrl_otf_base_vseq;
  `uvm_object_utils(flash_ctrl_serr_counter_vseq)
  `uvm_object_new

  constraint ctrl_num_c { ctrl_num dist { CTRL_TRANS_MIN := 7, [2:31] :/ 1, CTRL_TRANS_MAX := 2}; }
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
    int bank;

    ctrl.partition = FlashPartData;
    cfg.clk_rst_vif.wait_clks(5);

    fork
       begin
        repeat(50) begin
          `DV_CHECK_RANDOMIZE_FATAL(this)
          bank = $urandom_range(0, 1);
          ctrl.partition  = FlashPartData;
          ctrl.otf_addr = is_addr_odd * 4;
          randcase
            1:prog_flash(ctrl, bank, ctrl_num, fractions);
            1:read_flash(ctrl, bank, ctrl_num, fractions);
          endcase
        end
      end
      begin
         for (int i = 0; i < 5; ++i) begin
            fork
              send_rand_host_rd();
            join_none
            #0;
         end
         csr_utils_pkg::wait_no_outstanding_access();
      end
    join

  endtask // body
  task post_body();
    uvm_reg_data_t data;
    csr_rd(.ptr(ral.ecc_single_err_cnt[0]), .value(data));
    `DV_CHECK_EQ(data[7:0], cfg.serr_cnt[0])
    `DV_CHECK_EQ(data[15:8], cfg.serr_cnt[1])
  endtask
endclass // flash_ctrl_serr_counter_vseq
