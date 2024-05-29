// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Send errored traffic with normal traffic.
// Asserted error traffics are three kinds
// 1. Oversized (more than 16 bus words) program traffic
// 2. Oversized Read traffic: issue rd_fifo read more than
//    it is supposed to.
// 3. Issue rd_fifo read without starting op.

class flash_ctrl_oversize_error_vseq extends flash_ctrl_otf_base_vseq;
  `uvm_object_utils(flash_ctrl_oversize_error_vseq)
  `uvm_object_new
  flash_op_t ctrl;
  int num, bank;

  virtual task body();
    cfg.scb_h.do_alert_check = 0;
    cfg.otf_scb_h.comp_off = 0;
    cfg.seq_cfg.avoid_prog_res_fault = 1'b0;

    fork
      begin
        repeat(cfg.otf_num_rw) begin
          if (cfg.stop_transaction_generators()) break;
          randcase
            cfg.otf_wr_pct: begin
              `DV_CHECK(try_create_prog_op(ctrl, bank, num), "Could not create a prog flash op")
              `uvm_info(`gfn, "Regular prog_flash", UVM_MEDIUM)
              prog_flash(ctrl, bank, num, fractions);
            end
            cfg.otf_rd_pct: begin
              `DV_CHECK_RANDOMIZE_FATAL(this)
              ctrl = rand_op;
              get_bank_and_num(ctrl, bank, num);
              read_flash(ctrl, bank, num, fractions);
            end
            cfg.otf_bwr_pct: begin
              `uvm_info("seq", $sformatf("inj:prog_err: %0d", fractions + 16), UVM_MEDIUM)
              cfg.seq_cfg.trigger_prog_res_fault = 1'b1;
              `DV_CHECK(try_create_prog_op(ctrl, bank, num), "Could not create a prog flash op")
              `uvm_info(`gfn, $sformatf("Bad write prog_flash: fractions=%d", fractions + 16),
                        UVM_MEDIUM)
              cfg.seq_cfg.trigger_prog_res_fault = 1'b0;
              cfg.seq_cfg.avoid_prog_res_fault = 1'b0;
              `DV_CHECK_GT(fractions, 16)
              prog_flash(ctrl, bank, 1, fractions);
              cfg.seq_cfg.avoid_prog_res_fault = 1'b1;
            end
            cfg.otf_brd_pct: begin
              int sz = $urandom_range(1, 16);
              `DV_CHECK_RANDOMIZE_FATAL(this)
              ctrl = rand_op;
              get_bank_and_num(ctrl, bank, num);
              randcase
                1: begin
                  `uvm_info("seq", $sformatf("inj:overread %0d",sz), UVM_MEDIUM)
                  overread(ctrl, bank, 1, sz);
                end
                4: begin
                  `uvm_info("seq", $sformatf("inj:read_err %0d", fractions + sz), UVM_MEDIUM)
                  read_flash(ctrl, bank, .num(1), .wd(fractions), .overrd(sz));
                end
              endcase
             end
          endcase
        end
      end
      begin
        for (int i = 0; i < cfg.otf_num_hr; ++i) begin
          fork
            send_rand_host_rd();
          join_none
          #0;
        end
        csr_utils_pkg::wait_no_outstanding_access();
      end
    join
  endtask

endclass
