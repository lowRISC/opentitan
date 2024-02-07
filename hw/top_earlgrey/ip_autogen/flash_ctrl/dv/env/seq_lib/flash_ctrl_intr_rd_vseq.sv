// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Send read only traffic with interrup mode.
// No protection is applied.
class flash_ctrl_intr_rd_vseq extends flash_ctrl_legacy_base_vseq;
  `uvm_object_utils(flash_ctrl_intr_rd_vseq)
  `uvm_object_new

  task pre_start();
    cfg.intr_mode = 1;
    cfg.skip_init = 1;

    super.pre_start();
  endtask
  virtual task body();
    flash_op_t ctrl;
    int num, bank;

    flash_program_data_c.constraint_mode(0);
    cfg.clk_rst_vif.wait_clks(5);
    fork
      begin
        for (int i = 0; i < 1000; ++i) begin
          fork
            send_rand_host_rd();
          join_none
          #0;
        end
        csr_utils_pkg::wait_no_outstanding_access();
      end
      begin
        repeat(100) begin
          `DV_CHECK_MEMBER_RANDOMIZE_FATAL(rand_op)
          ctrl = rand_op;
          if (ctrl.partition == FlashPartData) begin
            num = $urandom_range(1, 32);
          end else begin
            num = $urandom_range(1, InfoTypeSize[rand_op.partition >> 1]);
          end
          bank = rand_op.addr[OTFBankId];
          read_flash(ctrl, bank, num);
        end
      end
    join
  endtask
endclass // flash_ctrl_intr_rd_vseq
