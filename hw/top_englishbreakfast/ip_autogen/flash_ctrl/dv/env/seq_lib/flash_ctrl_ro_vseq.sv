// Copyright lowRISC contributors (OpenTitan project).
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
            // Max transfer size of info is 512Byte.
            if (num * fractions > 128) begin
              num = 128 / fractions;
            end
          end
          bank = rand_op.addr[OTFBankId];
          read_flash(ctrl, bank, num);
        end
      end
    join
  endtask

endclass // flash_ctrl_ro_vseq
