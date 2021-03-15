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

  rand bit wait_for_first_seed;

  constraint num_ops_c {
    num_ops dist {
    [1    : 1000] :/ 2,
    [1001 : 4000] :/ 2,
    [4001 : 5000] :/ 1
    };
  }

  constraint lc_esc_delay_c {
    lc_esc_delay dist {
      0               :/ 1,
      [1 : 1_000_000] :/ 4
    };
  }

  constraint wait_for_first_seed_c {
    wait_for_first_seed dist {
      0 :/ 1,
      1 :/ 4
    };
  }

  virtual task pre_start();
    super.pre_start();

    // configure the SRAM TLUL agent to wait at least 2 cycles before dropping a request,
    // ONLY if the transaction is configured to abort
    cfg.m_sram_cfg.allow_a_valid_drop_wo_a_ready = 1;
    cfg.m_sram_cfg.a_valid_len_min = 2;
    cfg.m_sram_cfg.a_valid_len_max = 10;
  endtask

  virtual task body();
    repeat(num_trans) begin

      bit sent_lc_escalate = 0;

      fork
        begin
          // randomly enable zero delays in the SRAM TLUL agent
          if ($urandom_range(0, 1)) cfg.set_sram_zero_delays();
          req_scr_key();
          csr_spinwait(.ptr(ral.status.scr_key_valid), .exp_data(1));
          `DV_CHECK_MEMBER_RANDOMIZE_FATAL(num_ops)
          do_rand_ops(.num_ops(num_ops), .abort(1));
        end
        begin
          // wait a random number of cycles then send a lc_escalation request.
          // check if reset is asserted as well to avoid issues further down the road

          if (wait_for_first_seed) csr_spinwait(.ptr(ral.status.scr_key_valid), .exp_data(1));

          #lc_esc_delay;

          if (!cfg.under_reset) begin
            cfg.lc_vif.drive_lc_esc_en(lc_ctrl_pkg::On);
            sent_lc_escalate = 1;
          end
        end
      join

      // if lc escalation request was sent, then we need to perform some extra memory accesses
      if (sent_lc_escalate) begin
        bit [TL_DW-1:0] status;

        // after escalation request is seen, it takes 3 cycles to propagate from
        // `sram_ctrl` to the `prim_1p_ram_scr`, and 1 more cycle to update the CSRs
        cfg.clk_rst_vif.wait_clks(LC_ESCALATION_PROPAGATION_CYCLES + 1);

        csr_utils_pkg::wait_no_outstanding_access();

        fork
          begin
            // read out STATUS csr, scoreboard will check that proper updates have been made
            csr_rd(.ptr(ral.status), .value(status));
            csr_wr(.ptr(ral.status), .value(status));

            `uvm_info(`gfn,
              $sformatf("Performing %0d random memory accesses after LC escalation request",
                        num_ops_after_reset),
              UVM_HIGH)
            do_rand_ops(.num_ops(num_ops_after_reset), .blocking(1), .abort(1));

            // reset to get the DUT out of terminal state
            apply_reset();
          end
          begin
            // randomly drop the escalation request, should remain latched by design
            `DV_CHECK_MEMBER_RANDOMIZE_FATAL(lc_esc_delay)
            #lc_esc_delay;
            cfg.lc_vif.drive_lc_esc_en(lc_ctrl_pkg::Off);
          end
        join

        `uvm_info(`gfn,
          $sformatf("Performing %0d random memory accesses after reset", num_ops_after_reset),
          UVM_HIGH)
        do_rand_ops(.num_ops(num_ops_after_reset), .blocking(1));
      end
    end
  endtask

endclass
