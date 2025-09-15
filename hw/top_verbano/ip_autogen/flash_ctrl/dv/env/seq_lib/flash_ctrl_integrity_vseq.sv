// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Directed test to check flash_ctrl.single_err_addr
// Each round test insert one single bit error and capture the address from tb.
// At the end of each round, compare the captured value with
// csr read (flash_ctrl.single_err_addr) value.
class flash_ctrl_integrity_vseq extends flash_ctrl_otf_base_vseq;
  `uvm_object_utils(flash_ctrl_integrity_vseq)
  `uvm_object_new

  constraint ctrl_num_c {
    ctrl_num dist { CtrlTransMin := 7, [2:31] :/ 1, CtrlTransMax := 2};
  }
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
        repeat(100) begin
          if (cfg.stop_transaction_generators()) break;
          randcase
            1: begin
              `DV_CHECK(try_create_prog_op(ctrl, bank, num), "Could not create a prog flash op")
              prog_flash(ctrl, bank, num, fractions);
            end
            1: begin
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
        for (int i = 0; i < 10; ++i) begin
          fork
            send_rand_host_rd();
          join_none
          #0;
        end
        csr_utils_pkg::wait_no_outstanding_access();
      end
    join
  endtask : body
endclass : flash_ctrl_integrity_vseq
