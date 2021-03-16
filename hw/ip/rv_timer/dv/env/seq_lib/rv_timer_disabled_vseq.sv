// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence check no activity on timer register and interrupt when timer
// is disabled

class rv_timer_disabled_vseq extends rv_timer_random_vseq;
  `uvm_object_utils(rv_timer_disabled_vseq)
  `uvm_object_new

  task body();
    for (int trans = 1; trans <= num_trans; trans++) begin
      bit stop_reading;
      `uvm_info(`gfn, $sformatf("Running test iteration %0d/%0d", trans, num_trans), UVM_LOW)

      `DV_CHECK_RANDOMIZE_FATAL(this)

      // disable timers
      csr_wr(.ptr(ral.ctrl), .value(ral.ctrl.get_reset()));

      // configure the timers and harts based on rand fields
      cfg_all_timers();

      fork
        begin
          for (int i = 0; i < NUM_HARTS; i++) begin
            for (int j = 0; j < NUM_TIMERS; j++) begin
              automatic int a_i = i;
              automatic int a_j = j;
              fork
                begin
                  // wait for num clks required to expect interrupt
                  int    intr_pin_idx = a_i * NUM_TIMERS + a_j;
                  uint64 mtime_diff   = compare_val[a_i][a_j] - timer_val[a_i];
                  int    num_clks     = ((mtime_diff / step[a_i]) + 1) * (prescale[a_i] +1) + 1;
                  cfg.clk_rst_vif.wait_clks(num_clks);
                  `DV_CHECK_CASE_EQ(cfg.intr_vif.sample_pin(.idx(intr_pin_idx)), 1'b0)
                end
              join_none
            end
          end
          wait fork;
          stop_reading = 1'b1;
        end
        begin
          uint64 read_data;
          // Read intr status and timer_val reg randomly
          // Read will trigger check in scoreboard
          forever begin
            `DV_CHECK_MEMBER_RANDOMIZE_FATAL(delay)
            #(delay * 1ns);
            for (int i = 0; i < NUM_HARTS; i++) begin
              read_intr_status_reg(.hart(i), .status_val(read_data));
              read_timer_val_reg(.hart(i), .mtime_val(read_data));
            end
            if (stop_reading == 1) break;
          end
          // last read
          for (int i = 0; i < NUM_HARTS; i++) begin
            read_intr_status_reg(.hart(i), .status_val(read_data));
            read_timer_val_reg(.hart(i), .mtime_val(read_data));
          end
        end
      join
    end
  endtask : body

endclass : rv_timer_disabled_vseq
