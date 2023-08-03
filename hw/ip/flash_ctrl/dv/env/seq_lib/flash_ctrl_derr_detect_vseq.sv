// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Directed test to detect double bit error.
class flash_ctrl_derr_detect_vseq extends flash_ctrl_otf_base_vseq;
  `uvm_object_utils(flash_ctrl_derr_detect_vseq)
  `uvm_object_new

  virtual task body();
    flash_op_t ctrl;
    int num, bank;
    int fatal_cnt = 0;
    uvm_reg_data_t addr0, addr1;
    cfg.derr_once = 1;
    cfg.scb_h.do_alert_check = 1;
    cfg.m_tl_agent_cfg.check_tl_errs = 0;
    cfg.m_tl_agent_cfgs["flash_ctrl_eflash_reg_block"].check_tl_errs = 0;
    cfg.otf_scb_h.stop = 0;
    cfg.clk_rst_vif.wait_clks(5);

    fork begin : isolation_fork
      fork
        begin
          repeat(40) begin
            `DV_CHECK_RANDOMIZE_FATAL(this)
            ctrl = rand_op;
            bank = rand_op.addr[OTFBankId];
            if (ctrl.partition == FlashPartData) begin
              num = ctrl_num;
            end else begin
              num = ctrl_info_num;
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
          for (int i = 0; i < 4; ++i) begin
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
    end // block: isolation_fork
    join

    // Add drain time
    #10us;
    if (cfg.derr_created[0] + cfg.derr_created[1] > 0) begin
      fatal_cnt = cfg.scb_h.alert_count["fatal_err"];
      `DV_CHECK_NE(fatal_cnt, 0, "fatal alert is not detected",
                   error, "SEQ")
    end
    `uvm_info("SEQ", $sformatf("seqend derr_created: %p", cfg.derr_created), UVM_LOW)
    otf_tb_clean_up();
  endtask // body
endclass // flash_ctrl_derr_detect_vseq
