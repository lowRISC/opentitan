// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence update timer configuration while its active/running, this
// includes updating mtime, mtimecmp. Randomly step and prescale updated
// after disabling timer.

class rv_timer_cfg_update_on_fly_vseq extends rv_timer_sanity_vseq;
  `uvm_object_utils(rv_timer_cfg_update_on_fly_vseq)
  `uvm_object_new

  // Defing min clocks to have room to update timer cfg
  uint64 min_clks_until_expiry = 10_000;

  constraint ticks_c {
    solve prescale before ticks;
    foreach (ticks[i]) {
      if (en_harts[i]) {
        (ticks[i] * prescale[i]) <= max_clks_until_expiry;
        (ticks[i] * prescale[i]) >= min_clks_until_expiry;
      }
    }
  }

  constraint num_trans_c {
    num_trans inside {[1:4]};
  }

  task body();
    for (int trans = 1; trans <= num_trans; trans++) begin
      `uvm_info(`gfn, $sformatf("Running test iteration %0d/%0d", trans, num_trans), UVM_LOW)

      // disable timers
      csr_wr(.csr(ral.ctrl), .value(ral.ctrl.get_reset()));

      for (int hart = 0; hart < NUM_HARTS; hart++) begin
        for (int timer = 0; timer < NUM_TIMERS; timer++) begin
          int    num_clks;
          uint   read_data;
          uint64 mtime_diff;

          `DV_CHECK_RANDOMIZE_FATAL(this)

          // configure the timer cfg for particular timer
          cfg_all_timers();

          // enable timers
          cfg_timer(.hart(hart), .timer(timer), .enable(1'b1));

          // Wait for random num of clks before updating timer cfg
          num_clks = calculate_num_clks(hart, timer);
          status_read_for_clks(.hart(hart), .clks($urandom_range((num_clks / 10), (num_clks / 2))));

          // update timer cfg
          if ($urandom_range(0, 1)) begin
            // update either step or prescale
            if ($urandom_range(0, 1)) begin
              `uvm_info(`gfn, "Updating timer step value", UVM_LOW)
              step[hart] = $urandom_range(1, max_step);
            end
            else begin
              `uvm_info(`gfn, "Updating timer prescale value", UVM_LOW)
              prescale[hart] = $urandom_range(1, max_prescale);
            end
            // disable timer, update cfg, re enable timer
            cfg_timer(.hart(hart), .timer(timer), .enable(1'b0));
            cfg_hart(.hart(hart), .prescale(prescale[hart]), .step(step[hart]));
            cfg_timer(.hart(hart), .timer(timer), .enable(1'b1));
          end

          if ($urandom_range(0, 1)) begin
            `uvm_info(`gfn, "Updating timer compare value", UVM_LOW)
            mtime_diff = compare_val[hart][timer] - timer_val[hart];
            if ($urandom_range(0, 1)) begin
              compare_val[hart][timer] += $urandom_range((mtime_diff / 20), mtime_diff);
            end
            else begin
              compare_val[hart][timer] -= $urandom_range((mtime_diff / 20), (mtime_diff / 4));
            end
            set_compare_val(.hart(hart), .timer(timer), .val(compare_val[hart][timer]));
          end

          if ($urandom_range(0, 1)) begin
            `uvm_info(`gfn, "Updating timer value", UVM_LOW)
            mtime_diff = compare_val[hart][timer] - timer_val[hart];
            if ($urandom_range(0, 1)) begin
              timer_val[hart] += $urandom_range((mtime_diff / 20), (mtime_diff / 4));
            end
            else begin
              timer_val[hart] -= $urandom_range((mtime_diff / 20), mtime_diff);
            end
            set_timer_val(.hart(hart), .val(timer_val[hart]));
          end

          // Read timer val reg to get latest value of timer for calc of num_clks
          read_timer_val_reg(.hart(hart), .mtime_val(timer_val[hart]));
          num_clks = calculate_num_clks(hart, timer);

          // random read till for clks = (num_clks - (prescale[hart] + 4))
          // Subtract prescale to avoid having reg read and timer expire in same time
          status_read_for_clks(.hart(hart), .clks(num_clks - (prescale[hart] + 4)));

          // wait for (prescale[*] + 5) to let timer expire as per new cfg,
          // one clock extra to avoid race condition btw scoreboard predict and seq reg read
          cfg.clk_rst_vif.wait_clks(prescale[hart] + 5);

          `uvm_info(`gfn, $sformatf("Timer expired last read"), UVM_LOW)
          read_intr_status_reg(.hart(hart), .status_val(read_data));
          `DV_CHECK_EQ_FATAL(read_data, (1 << timer))

          // disable timers and clear interrupt
          cfg_timer(.hart(hart), .timer(timer), .enable(1'b0));
          clear_intr_state(.hart(hart), .timer(timer));
        end
      end
    end
  endtask : body

endclass : rv_timer_cfg_update_on_fly_vseq
