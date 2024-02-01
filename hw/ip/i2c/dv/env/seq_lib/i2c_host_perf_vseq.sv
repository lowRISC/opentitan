// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Test to check if the bitrate of data transfer matches the bitrate specified for each mode of I2C
// Sequence:
// > Constrain the mode of I2C (Standard/Fast/FastPlus)
// > Constrain the timing parameters to use the minimum values specified in I2C spec for the mode
// > Issue random number of Read or Write transactions
// > Calculate the bit rate using programmed timing parameters
// > Check if generated SCL period is as expected
class i2c_host_perf_vseq extends i2c_rx_tx_vseq;
  `uvm_object_utils(i2c_host_perf_vseq)
  `uvm_object_new

  parameter real PERFTHRESHOLD = 0.80; // Threshold for performance comparison
  rand speed_mode_e           speed_mode;
  rand uint                   scl_frequency; //in KHz
  rand uint                   scl_period; // converted to register value
  real                        last_posedge; // Last posedge time of SCL in ns
  uint                        scl_period_observed; // observed SCL period in ns
  uint                        scl_period_expected; // observed SCL period in ns
  uint                        coerced_scl_period; // Actual SCL period, in cycles
  uint                        coerced_scl_frequency; // Actual SCL frequency, given parameters

  constraint num_trans_c {
    num_trans  == 5;
  }

  // Ensure the input clock frequency is high enough to meet minimum thigh and
  // tlow cycle counts for a given mode (i.e. 125 ns or 8 MHz)
  constraint min_peri_clk_period_c {
    solve cfg.clk_freq_mhz before speed_mode;
    if (cfg.clk_freq_mhz < 4) {
      speed_mode == Standard;
    } else if (cfg.clk_freq_mhz < 8) {
      // For Fast, need at least 4 MHz's tlow=6, thigh=3, t_r=2, t_f=2 to
      // satisfy all specs AND have minimum of 3 cycles for tlow and thigh to
      // satisfy the round-trip time. This yields a nominal i2c frequency of
      // 325 kHz.
      speed_mode inside {Standard, Fast};
    } else {
      // For FastPlus, need at least tlow=4, thigh=3, t_r=1, t_f=1 to satisfy
      // all specs with high enough thigh and tlow to satisfy the round-trip
      // time (both greater than 3 cycles). That is at 8 MHz input clock and
      // yields a nominal i2c frequency of 889 kHz.
      speed_mode inside {Standard, Fast, FastPlus};
    }
  }

  // Set the nominal frequency. The true, coerced value will be determined in
  // post_randomize(), along with the coerced_scl_period.
  constraint scl_frequency_c {
    solve speed_mode before scl_frequency;
    if(speed_mode == Standard){
      scl_frequency == 100;
    }else if(speed_mode == Fast) {
      scl_frequency == 400;
    }else if(speed_mode == FastPlus) {
      scl_frequency == 1000;
    }
  }

  constraint scl_period_c{
    solve scl_frequency before scl_period;
    scl_period == ((10**9)/scl_frequency)/(cfg.clk_rst_vif.clk_period_ps);
  }

// Constrain the timing parameters based on programmers guide
  constraint timing_val_c {
    thd_sta == cfg.seq_cfg.get_thdsta_min(speed_mode, cfg.clk_rst_vif.clk_period_ps);
    tsu_sto == cfg.seq_cfg.get_tsusto_min(speed_mode, cfg.clk_rst_vif.clk_period_ps);
    tsu_dat == cfg.seq_cfg.get_tsudat_min(speed_mode, cfg.clk_rst_vif.clk_period_ps);
    tsu_sta == cfg.seq_cfg.get_tsusta_min(speed_mode, cfg.clk_rst_vif.clk_period_ps);
    if (cfg.seq_cfg.get_thddat_min(speed_mode, cfg.clk_rst_vif.clk_period_ps) > 0) {
      thd_dat == cfg.seq_cfg.get_thddat_min(speed_mode, cfg.clk_rst_vif.clk_period_ps);
    } else {
      thd_dat == 1;
    }
    solve speed_mode before tlow, t_r, t_f, thd_sta, tsu_sto, tsu_dat, thd_dat,
                            tsu_sta, t_buf, thigh;

    solve scl_period before tlow, thigh, t_f, t_r;
    solve t_r before tlow;
    solve t_f before tlow;
    solve thigh before tlow;
    solve tsu_sta before tlow;
    solve thd_dat before tlow;
    solve t_r before t_buf;
    solve tsu_dat before t_buf;
    // tlow must be at least 2 greater than the sum of t_r + tsu_dat + thd_dat
    // because the flopped clock (see #15003 below) reduces tClockLow by 1.

    // Due to remainders after dividing each of the four components into the
    // peripheral clock period, the SCL cycle count may have to float to as
    // many as four cycles longer than the ideal (an effect of a ceil()
    // operation on each component).
    tlow <= 4 + scl_period - t_r - t_f - thigh;
    tlow >= scl_period - t_r - t_f - thigh;

    tlow > (t_r + tsu_dat + thd_dat + 1);
    tlow > thd_dat - t_f;
    t_buf == tsu_sta - t_r + 1;

    // Minimum values to accommodate round-trip latency through the IP.
    tlow  >= 3;
    thigh >= 3;
    // Spec minimum value of parameters
    tlow  >= cfg.seq_cfg.get_tlow_min(speed_mode, cfg.clk_rst_vif.clk_period_ps);
    t_r   >= cfg.seq_cfg.get_tr_min(speed_mode, cfg.clk_rst_vif.clk_period_ps);
    t_f   >= cfg.seq_cfg.get_tf_min(speed_mode, cfg.clk_rst_vif.clk_period_ps);
    thigh >= cfg.seq_cfg.get_thigh_min(speed_mode, cfg.clk_rst_vif.clk_period_ps);
    // Spec maximum value of parameters
    t_r <= cfg.seq_cfg.get_tr_max(speed_mode, cfg.clk_rst_vif.clk_period_ps);
    t_f <= cfg.seq_cfg.get_tf_max(speed_mode, cfg.clk_rst_vif.clk_period_ps);

    t_sda_unstable     == 0;
    t_sda_interference == 0;
    t_scl_interference == 0;
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

  virtual task pre_start();
    super.pre_start();
    `uvm_info(`gfn, $sformatf("speed_mode = %s", speed_mode.name()), UVM_LOW)
    `uvm_info(`gfn, $sformatf("scl_frequency = %d KHz", coerced_scl_frequency), UVM_LOW)
    `uvm_info(`gfn, $sformatf("clk_period_ps = %dps", cfg.clk_rst_vif.clk_period_ps), UVM_MEDIUM)
    `uvm_info(`gfn, $sformatf("(scl_period/clk_period) = %d ", coerced_scl_period), UVM_MEDIUM)
    perf_monitor();
    print_time_property();
  endtask

  // Disable randomization of timing parameters after first randomize call
  function void post_randomize();
    tlow.rand_mode(0);
    thd_sta.rand_mode(0);
    tsu_sta.rand_mode(0);
    thd_dat.rand_mode(0);
    tsu_dat.rand_mode(0);
    t_buf.rand_mode(0);
    tsu_sto.rand_mode(0);
    t_r.rand_mode(0);
    t_f.rand_mode(0);
    thigh.rand_mode(0);
    // Coerce value after quantization. Actual frequency is different from the
    // randomized setting, due to the granularity of the dividers.
    coerced_scl_period = t_r + t_f + thigh + tlow;
    coerced_scl_frequency = 10**9/(coerced_scl_period*cfg.clk_rst_vif.clk_period_ps);
  endfunction

  // Task to calculate the SCL period
  virtual task perf_monitor();
    bit first_scl_posedge = 1;
    scl_period_expected = (1e6 / coerced_scl_frequency);
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
    uint bit_rate; // in Kbps
    real end_time = $realtime;
    // env_cfg must be reset after vseq completion
    cfg.reset_seq_cfg();
    super.post_start();
    print_seq_cfg_vars("post-start");
    `uvm_info(`gfn, $sformatf("scl_period_observed = %0dns", scl_period_observed), UVM_MEDIUM)
    `uvm_info(`gfn, $sformatf("scl_period_expected = %0dns", scl_period_expected), UVM_MEDIUM)
    if (scl_period_expected < PERFTHRESHOLD * scl_period_observed) begin
      `uvm_error(`gfn, "DUT not working as expected")
    end
  endtask


endclass : i2c_host_perf_vseq
