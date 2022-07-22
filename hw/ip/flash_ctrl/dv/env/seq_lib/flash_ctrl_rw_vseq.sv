// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class flash_ctrl_rw_vseq extends flash_ctrl_otf_base_vseq;
  `uvm_object_utils(flash_ctrl_rw_vseq)
  `uvm_object_new

  virtual task body();
    flash_op_t ctrl;
    int bank;

    ctrl.partition = FlashPartData;
    cfg.clk_rst_vif.wait_clks(5);

    fork
      begin
        repeat(250) begin
          `DV_CHECK_RANDOMIZE_FATAL(this)
          bank = $urandom_range(0, 1);
          randcase
            1:prog_flash(ctrl, bank, ctrl_num);
            1:read_flash(ctrl, bank, ctrl_num);
          endcase
        end
      end
      begin
        for (int i = 0; i < 2500; ++i) begin
          fork
            send_rand_host_rd();
          join_none
          #0;
        end
        csr_utils_pkg::wait_no_outstanding_access();
      end
    join
  endtask
endclass // flash_ctrl_rw_vseq
