// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence creates only one double bit error at random time.
class flash_ctrl_derr_detect_vseq extends flash_ctrl_otf_base_vseq;
  `uvm_object_utils(flash_ctrl_derr_detect_vseq)
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
    int fatal_cnt = 0;
    uvm_reg_data_t addr0, addr1;
    cfg.derr_once = 1;
    cfg.scb_h.do_alert_check = 1;
    cfg.m_tl_agent_cfg.check_tl_errs = 0;
    cfg.m_tl_agent_cfgs["flash_ctrl_eflash_reg_block"].check_tl_errs = 0;

    ctrl.partition = FlashPartData;
    otf_tb_clean_up();
    cfg.clk_rst_vif.wait_clks(5);

    fork
      begin
        repeat(20) begin
          `DV_CHECK_RANDOMIZE_FATAL(this)
          bank = $urandom_range(0, 1);
          ctrl.partition  = FlashPartData;
          ctrl.otf_addr += (is_addr_odd * 4);
          randcase
            1:prog_flash(ctrl, bank, ctrl_num, fractions);
            1:read_flash(ctrl, bank, ctrl_num, fractions);
          endcase
        end
      end
      begin
        for (int i = 0; i < 3; ++i) begin
          fork
            send_rand_host_rd();
          join_none
          #0;
        end
        csr_utils_pkg::wait_no_outstanding_access();
      end
      begin
        while (cfg.scb_h.alert_count["fatal_err"] == 0) begin
          cfg.clk_rst_vif.wait_clks(1);
        end
        dut_init();
      end
    join_any
    disable fork;
    if (cfg.derr_created[0] + cfg.derr_created[1] > 0) begin
      fatal_cnt = cfg.scb_h.alert_count["fatal_err"];
      `DV_CHECK_NE(fatal_cnt, 0, "fatal alert is not detected",
                   error, "SEQ")
    end
    `uvm_info("SEQ", $sformatf("seqend derr_created: %p", cfg.derr_created), UVM_LOW)
  endtask // body
endclass // flash_ctrl_serr_address_vseq
