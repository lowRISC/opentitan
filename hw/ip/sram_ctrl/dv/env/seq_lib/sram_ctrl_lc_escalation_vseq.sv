// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// In this sequence, we randomly send a lifecycle escalation during operation of some memory
// transactions, which is expected lock up the SRAM memory.
// We then send some more memory requests, none of which should complete successfully.
// Then, we reset the design to get the SRAM out of the terminal state, and then do a small number
// of memory operations to verify that things are back up and functioning properly.
class sram_ctrl_lc_escalation_vseq extends sram_ctrl_multiple_keys_vseq;

  `uvm_object_utils(sram_ctrl_lc_escalation_vseq)
  `uvm_object_new

  rand int lc_esc_delay;

  constraint lc_esc_delay_c {
    lc_esc_delay dist {
      0            :/ 1,
      [1 : 10_000] :/ 4
    };
  }

  virtual task pre_start();
    super.pre_start();

    // configure the SRAM TLUL agent to wait at least 2 cycles before dropping a request,
    // ONLY if the transaction is configured to abort
    cfg.m_tl_agent_cfgs[cfg.sram_ral_name].allow_a_valid_drop_wo_a_ready = 1;
    cfg.m_tl_agent_cfgs[cfg.sram_ral_name].a_valid_len_min = 2;
    cfg.m_tl_agent_cfgs[cfg.sram_ral_name].a_valid_len_max = 10;
  endtask

  virtual task body();
    repeat (num_trans) begin
      // randomly set init or renew key
      `DV_CHECK_RANDOMIZE_FATAL(ral.ctrl.init)

      // without init, stored intg isn't correct
      if (!ral.ctrl.init.get()) begin
        cfg.disable_d_user_data_intg_check_for_passthru_mem = 1;
      end
      `DV_CHECK_RANDOMIZE_FATAL(ral.ctrl.renew_scr_key)
      csr_update(.csr(ral.ctrl));

      do_rand_ops(.num_ops($urandom_range(10, 100)), .blocking(0), .abort(0),
                  .wait_complete(1));

      // any non-off value is treated as true
      cfg.lc_vif.drive_lc_esc_en(get_rand_lc_tx_val(.t_weight(1),
                                                    .f_weight(0),
                                                    .other_weight(1)));
      // After escalation, key becomes invalid and design returns invalid integrity
      cfg.disable_d_user_data_intg_check_for_passthru_mem = 1;

      `uvm_info(`gfn, "Esc_en is on", UVM_MEDIUM);

      // after escalation request is seen, it takes 3 cycles to propagate from
      // `sram_ctrl` to the `prim_1p_ram_scr`, and 1 more cycle to update the CSRs
      cfg.clk_rst_vif.wait_clks(LC_ESCALATION_PROPAGATION_CYCLES + 1);

      fork
        begin
          bit [TL_DW-1:0] status;
          // read out STATUS csr, scoreboard will check that proper updates have been made
          csr_rd(.ptr(ral.status), .value(status));
          csr_wr(.ptr(ral.status), .value(status));

          `uvm_info(`gfn,
            $sformatf("Performing %0d random memory accesses after LC escalation request",
                      num_ops_after_reset),
            UVM_HIGH)
          do_rand_ops(.num_ops(num_ops_after_reset), .blocking(0), .exp_err_rsp(1),
                      .wait_complete(1));

          // reset to get the DUT out of terminal state
          apply_reset();
        end
        begin
          // randomly drop the escalation request, should remain latched by design
          `DV_CHECK_MEMBER_RANDOMIZE_FATAL(lc_esc_delay)
          #lc_esc_delay;
          cfg.lc_vif.drive_lc_esc_en(lc_ctrl_pkg::Off);
          `uvm_info(`gfn, "Esc_en is off", UVM_MEDIUM);
        end
      join

      req_mem_init();
      `uvm_info(`gfn,
                $sformatf("Performing %0d random memory accesses after reset", num_ops_after_reset),
                UVM_HIGH)
      do_rand_ops(.num_ops(num_ops_after_reset), .blocking(1));
    end
  endtask

endclass
