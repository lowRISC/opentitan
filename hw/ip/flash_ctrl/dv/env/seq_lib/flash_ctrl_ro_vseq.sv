// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Send read only traffic
// No protection is applied.
class flash_ctrl_ro_vseq extends flash_ctrl_otf_base_vseq;
  `uvm_object_utils(flash_ctrl_ro_vseq)
  `uvm_object_new

  virtual task body();
    flash_op_t ctrl;
    int num, bank;

    ctrl.partition  = FlashPartData;
    cfg.clk_rst_vif.wait_clks(5);

    fork
      begin
        for (int i = 0; i < 10; ++i) begin
          fork
            send_rand_host_rd(, i);
          join_none
          #0;
        end
        `JDBG(("TEST: outstanding_access:%0d", csr_utils_pkg::outstanding_accesses))
        csr_utils_pkg::wait_no_outstanding_access();
      end
      begin
        repeat(100) begin
          num = 1;//$urandom_range(CTRL_TRANS_MIN, CTRL_TRANS_MAX);
          bank = 0;//$urandom_range(0, 1);
          read_flash(ctrl, bank, num);
        end
      end
    join
  endtask

endclass // flash_ctrl_ro_vseq
