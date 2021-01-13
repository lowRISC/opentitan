// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Randomly set keymgr_en to not On to test design should wipe all the secrets and enter StDisabled
class keymgr_lc_disable_vseq extends keymgr_random_vseq;
  `uvm_object_utils(keymgr_lc_disable_vseq)
  `uvm_object_new

  virtual task body();
    bit regular_vseq_done;

    fork
      disable_keymgr_after_random_delay(regular_vseq_done);
      begin
        super.body();
        // let the unblocking thread finish before ending the body
        regular_vseq_done = 1;
      end
    join
  endtask : body

  // disable keymgr after 3 kinds of random delay
  task disable_keymgr_after_random_delay(ref bit regular_vseq_done);
    uint delay_cycles;
    lc_ctrl_pkg::lc_tx_t lc_en;

    randcase
      // delay 0-5000 cycles, the length of most of simulation is 1000-10_000 cycles
      1: begin
        `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(delay_cycles,
                                           delay_cycles inside {[0:5000]};)
        cfg.clk_rst_vif.wait_clks(delay_cycles);
      end
      // wait until enter a random state and add some delay
      1: begin
        keymgr_pkg::keymgr_working_state_e state;
        `DV_CHECK_STD_RANDOMIZE_FATAL(state)
        csr_spinwait(.ptr(ral.working_state), .exp_data(state),
                     .spinwait_delay_ns($urandom_range(0, 1000)));

        `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(delay_cycles,
                                           delay_cycles dist {[0:10]     :/ 1,
                                                              [11:200]   :/ 1,
                                                              [201:2000] :/ 1};)
        cfg.clk_rst_vif.wait_clks(delay_cycles);
      end
      // wait for some delay and wait for a WIP operation, then add some small delay
      // so that lc_disable occurs during an operation
      1: begin
        `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(delay_cycles,
                                           delay_cycles inside {[0:5000]};)

        cfg.clk_rst_vif.wait_clks(delay_cycles);

        forever begin
          bit [TL_DW-1:0] op_status_val;
          csr_rd(ral.op_status, op_status_val);

          if (op_status_val == keymgr_pkg::OpWip) break;
          else if (regular_vseq_done) return;

          cfg.clk_rst_vif.wait_clks($urandom_range(0, 100));
        end

        `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(delay_cycles,
                                           delay_cycles dist {[0:1]    :/ 1,
                                                              [2:10]   :/ 1,
                                                              [11:100] :/ 1};)
        cfg.clk_rst_vif.wait_clks(delay_cycles);
      end
    endcase

    // keymgr_en is async
    #($urandom_range(0, cfg.clk_rst_vif.clk_period_ps) * 1ps);

    // set keymgr_en to not On, which is disabled
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(lc_en,
                                       lc_en != lc_ctrl_pkg::On;)
    cfg.keymgr_vif.keymgr_en = lc_en;
  endtask : disable_keymgr_after_random_delay

endclass : keymgr_lc_disable_vseq
