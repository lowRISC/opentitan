// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Test to check if the bitrate of data transfer matches the bitrate specified for each mode of I2C.
// - Bitrate is only measured in terms of the SCL frequency, ignoring control bits and start/stop.
//
// Sequence:
// > Constrain the mode of I2C (Standard/Fast/FastPlus)
// > Constrain the timing parameters to use the minimum values specified in I2C spec for the mode
// > Issue random number of Read or Write transactions
// > Calculate the bit rate using programmed timing parameters
// > Check if generated SCL period is as expected

class i2c_host_perf_vseq extends i2c_rx_tx_vseq;
  `uvm_object_utils(i2c_host_perf_vseq)

  parameter real PERFTHRESHOLD = 0.80; // Threshold for performance comparison
  rand speed_mode_e           speed_mode;
  rand uint                   scl_frequency; //in KHz
  rand uint                   scl_period; // converted to register value
  real                        last_posedge; // Last posedge time of SCL in ns
  uint                        scl_period_observed; // observed SCL period in ns
  uint                        scl_period_expected; // observed SCL period in ns

  constraint num_trans_c {
    num_trans  == 5;
  }

  // should have few long transactions
  constraint num_wr_bytes_c {
    num_wr_bytes dist {
      1       :/ 1,
      [2:8]   :/ 1,
      [9:32]  :/ 1,
      256     :/ 1
    };
  }
  // num_rd_bytes = 0: read transaction length is 256b bytes
  constraint num_rd_bytes_c {
    num_rd_bytes dist {
      0       :/ 1,
      1       :/ 1,
      [2:8]   :/ 1,
      [9:32]  :/ 1
    };
  }

  // clear interrupt immediately
  constraint clear_intr_dly_c { clear_intr_dly == 0; }

  // set latency to zero values for fatest access fmt_fifo and rx_fifo
  constraint fmt_fifo_access_dly_c { fmt_fifo_access_dly == 0;}
  constraint rx_fifo_access_dly_c  { rx_fifo_access_dly  == 0;}

  class host_perf_timing_cfg extends i2c_timing_cfg;
    constraint maxperf_c {
      // To constrain for maximium performance:
      // - Setup/Hold times can be given their minimum possible values.
      // - Other params can float anywhere in their valid ranges
      // - Limiting the total SCL period during data transfer (tlow + tr + thigh + tf) per the speedmode

      // 'scl_period_ratio' is the clock period of the maximum frequency for the speedmode selected.
      // - However, the SCL cycle count may have to float to as many as four cycles longer than the ideal (an effect of a ceil() operation on each component).
      //   This is due to remainders after dividing each of the four components into the peripheral clock period.
      tc.tlow + tc.t_r + tc.thigh + tc.t_f >= scl_period_ratio;
      tc.tlow + tc.t_r + tc.thigh + tc.t_f <= scl_period_ratio + 4;
    }
  endclass : host_perf_timing_cfg

  /////////////
  // METHODS //
  /////////////

  function new (string name = "");
    host_perf_timing_cfg hptc = new;
    super.new(name);
    `downcast(tcc, hptc);
    // Disable the baseclass constraints, as they would conflict.
    tcc.timing_val_minmax_c.constraint_mode(0);
    tcc.tsu_sta_minmax_c.constraint_mode(0);
    tcc.error_stimulus_c.constraint_mode(0); // No errors
    tcc.spec_minimums_c.constraint_mode(1); // Force spec minimums
  endfunction : new

  virtual task pre_start();
    super.pre_start();
    perf_monitor();
  endtask

  // Task to calculate the SCL period
  virtual task perf_monitor();
    bit first_scl_posedge = 1;
    fork
      forever begin
        @(posedge cfg.m_i2c_agent_cfg.vif.scl_i);
        if (first_scl_posedge) begin
          last_posedge = $realtime;
          first_scl_posedge = 0;
        end
        else begin
          real current_posedge = $realtime;
          scl_period_observed = uint'(current_posedge - last_posedge);
          last_posedge = current_posedge;
        end
      end
    join_none
  endtask

  virtual task post_start();
    // env_cfg must be reset after vseq completion
    cfg.reset_seq_cfg();
    super.post_start();
    print_seq_cfg_vars("post-start");
    begin
      uint scl_period_expected = (tcc.coerced_scl_period_cycles * (1s / tcc.f_clk_i));
      `uvm_info(`gfn, $sformatf("scl_period_observed = %0dns", scl_period_observed), UVM_MEDIUM)
      `uvm_info(`gfn, $sformatf("scl_period_expected = %0dns", scl_period_expected), UVM_MEDIUM)
      if (scl_period_expected < PERFTHRESHOLD * scl_period_observed) begin
        `uvm_error(`gfn, "DUT not working as expected")
      end
    end
  endtask


endclass : i2c_host_perf_vseq
