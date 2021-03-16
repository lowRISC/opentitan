// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence update timer configuration while its active/running, this
// includes updating mtime, mtimecmp. Randomly step and prescale updated
// after disabling timer. This seq also exercise upating timer cfg multiple
// times when timer is close to expire (1 prescale before).

class rv_timer_cfg_update_on_fly_vseq extends rv_timer_random_vseq;
  `uvm_object_utils(rv_timer_cfg_update_on_fly_vseq)
  `uvm_object_new

  rand bit upd_cfg_in_end;

  // Defing min clocks to have room to update timer cfg
  uint64 min_clks_until_expiry = 10_000;

  constraint ticks_c {
    solve prescale before ticks;
    foreach (ticks[i]) {
      if (en_harts[i]) {
        (ticks[i] * (prescale[i] + 1)) <= max_clks_until_expiry;
        (ticks[i] * (prescale[i] + 1)) >= min_clks_until_expiry;
      }
    }
  }

  constraint num_trans_c {
    num_trans inside {[1:4]};
  }

  function void pre_randomize();
    super.pre_randomize();
    max_clks_until_expiry = 1_000_000; // Redefining max clock to avoid timeout
  endfunction

  task body();
    for (int trans = 1; trans <= num_trans; trans++) begin
      `uvm_info(`gfn, $sformatf("Running test iteration %0d/%0d", trans, num_trans), UVM_LOW)

      // disable timers
      csr_wr(.ptr(ral.ctrl), .value(ral.ctrl.get_reset()));

      for (int hart = 0; hart < NUM_HARTS; hart++) begin
        for (int timer = 0; timer < NUM_TIMERS; timer++) begin
          int    num_clks;
          uint   read_data;
          bit timer_at_min_max_val;

          `DV_CHECK_RANDOMIZE_FATAL(this)

          // configure the timer cfg for particular timer
          cfg_all_timers();

          // enable timers
          cfg_timer(.hart(hart), .timer(timer), .enable(1'b1));

          repeat (upd_cfg_in_end ? $urandom_range(4, 8) : 1) begin

            // Wait and read intr status for clks before updating timer cfg
            num_clks = calculate_num_clks(hart, timer);
            if (upd_cfg_in_end) begin
              // subtract one prescale value i.e.(prescale+1) +
              // 8 (clks to update timer and compare val) + 2 (read timer val)
              num_clks -= (prescale[hart] + 1) + 8 + 2;
            end
            else begin
              num_clks = $urandom_range((num_clks / 10), (num_clks / 2));
            end
            status_read_for_clks(.hart(hart), .clks(num_clks));

            // update timer cfg (step/prescale)
            if (!upd_cfg_in_end & $urandom_range(0, 1)) begin
              // update either step or prescale
              if ($urandom_range(0, 1)) begin
                `uvm_info(`gfn, "Updating timer step value", UVM_LOW)
                step[hart] = $urandom_range(1, max_step);
              end
              else begin
                `uvm_info(`gfn, "Updating timer prescale value", UVM_LOW)
                prescale[hart] = $urandom_range(0, max_prescale);
              end
              // disable timer, update cfg, re enable timer
              cfg_timer(.hart(hart), .timer(timer), .enable(1'b0));
              cfg_hart(.hart(hart), .prescale(prescale[hart]), .step(step[hart]));
              cfg_timer(.hart(hart), .timer(timer), .enable(1'b1));
            end

            // update timer and compare reg
            // bypass updating timer and compare reg if values are close to
            // zero or max and may get overflow or empty after random update
            // max_compare_val is calculated using max random value added to
            // compare_val without overflowing with below randomization which is
            // ((1 << 64)-1) - (max_step_value*300) = 'hFFFFFFFFFFFED52B
            // min_timer_val is calculated using max random value subtracted from
            // timer_val with below randomiztion which is (max_step_value*300) = 'h12AD4
            if ((compare_val[hart][timer] >= 64'hFFFFFFFFFFFED52B) |
                (timer_val[hart] <= 64'h12AD4)) begin
              timer_at_min_max_val = 1'b1;
              break;
            end
            else begin
              uint64 mtime_diff;
              `uvm_info(`gfn, "Updating timer and compare reg", UVM_LOW)
              mtime_diff = compare_val[hart][timer] - timer_val[hart];
              if (upd_cfg_in_end | $urandom_range(0, 1)) begin
                compare_val[hart][timer] += step[hart] * $urandom_range(30, 300);
              end
              else begin
                compare_val[hart][timer] -= mtime_diff / ($urandom_range(4, 20));
              end
              set_compare_val(.hart(hart), .timer(timer), .val(compare_val[hart][timer]));

              mtime_diff = compare_val[hart][timer] - timer_val[hart];
              if (!upd_cfg_in_end | $urandom_range(0, 1)) begin
                timer_val[hart] += mtime_diff / ($urandom_range(4, 20));
              end
              else begin
                timer_val[hart] -= step[hart] * $urandom_range(30, 300);
              end
              set_timer_val(.hart(hart), .val(timer_val[hart]));
            end
            // Read timer val reg to get latest value of timer for calc of num_clks
            read_timer_val_reg(.hart(hart), .mtime_val(timer_val[hart]));
          end

          // check for no intr asserted
          read_intr_status_reg(.hart(hart), .status_val(read_data));
          `DV_CHECK_EQ(read_data, 0)

          // random read till for clks = (num_clks - (prescale[hart] + 4))
          // Subtract prescale to avoid having reg read and timer expire at same time
          if (!(upd_cfg_in_end & timer_at_min_max_val)) begin
            num_clks = calculate_num_clks(hart, timer);
            status_read_for_clks(.hart(hart), .clks(num_clks - (prescale[hart] + 4)));
          end

          // wait for (prescale[*] + 5) to let timer expire as per new cfg,
          // one clock extra to avoid race condition btw scoreboard predict and seq reg read
          cfg.clk_rst_vif.wait_clks(prescale[hart] + 5);

          `uvm_info(`gfn, $sformatf("Timer expired last read"), UVM_LOW)
          read_intr_status_reg(.hart(hart), .status_val(read_data));
          `DV_CHECK_EQ_FATAL(read_data, (1 << timer))

          // clear intr status randomly while timer is still enable and check for sticky interrupt
          if ($urandom_range(0, 1)) clear_intr_state(.hart(hart), .timer(timer));

          // disable timers and clear interrupt
          cfg_timer(.hart(hart), .timer(timer), .enable(1'b0));
          clear_intr_state(.hart(hart), .timer(timer));
        end
      end
    end
  endtask : body

endclass : rv_timer_cfg_update_on_fly_vseq
