// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_base_vseq extends cip_base_vseq #(
    .CFG_T               (i2c_env_cfg),
    .RAL_T               (i2c_reg_block),
    .COV_T               (i2c_env_cov),
    .VIRTUAL_SEQUENCER_T (i2c_virtual_sequencer)
  );
  `uvm_object_utils(i2c_base_vseq)

  // class property
  local timing_cfg_t          timing_cfg;
  bit [7:0]                   rd_data;
  bit                         do_interrupt = 1'b1;
  bit                         force_use_incorrect_config = 1'b0;
  // random property
  rand uint                   fmt_fifo_access_dly;
  rand uint                   rx_fifo_access_dly;

  rand bit   [NumI2cIntr-1:0] en_intr;
  rand uint                   num_trans;
  rand uint                   num_wr_bytes;
  rand uint                   num_rd_bytes;
  rand bit   [7:0]            wr_data;
  rand bit   [6:0]            addr;
  rand bit                    rw_bit;
  i2c_item                    fmt_item;

  // timing property
  rand bit [15:0]             thigh;      // high period of the SCL in clock units
  rand bit [15:0]             tlow;       // low period of the SCL in clock units
  rand bit [15:0]             t_r;        // rise time of both SDA and SCL in clock units
  rand bit [15:0]             t_f;        // fall time of both SDA and SCL in clock units
  rand bit [15:0]             thd_sta;    // hold time for (repeated) START in clock units
  rand bit [15:0]             tsu_sta;    // setup time for repeated START in clock units
  rand bit [15:0]             tsu_sto;    // setup time for STOP in clock units
  rand bit [15:0]             tsu_dat;    // data setup time in clock units
  rand bit [15:0]             thd_dat;    // data hold time in clock units
  rand bit [15:0]             t_buf;      // bus free time between STOP and START in clock units
  rand bit [30:0]             t_timeout;  // max time target may stretch the clock
  rand bit                    e_timeout;  // max time target may stretch the clock

  // constraints
  constraint rw_bit_c    { rw_bit     inside {0, 1}; }
  constraint addr_c      { addr       inside {[I2C_MIN_ADDR : I2C_MAX_ADDR]}; }
  constraint wr_data_c   { wr_data    inside {[I2C_MIN_DATA : I2C_MAX_DATA]}; }
  constraint num_trans_c { num_trans  inside {[I2C_MIN_TRAN : I2C_MAX_TRAN]}; }

  constraint timing_val_c {
    thigh     inside { [I2C_MIN_TIMING : I2C_MAX_TIMING] };
    t_r       inside { [I2C_MIN_TIMING : I2C_MAX_TIMING] };
    t_f       inside { [I2C_MIN_TIMING : I2C_MAX_TIMING] };
    thd_sta   inside { [I2C_MIN_TIMING : I2C_MAX_TIMING] };
    tsu_sto   inside { [I2C_MIN_TIMING : I2C_MAX_TIMING] };
    tsu_dat   inside { [I2C_MIN_TIMING : I2C_MAX_TIMING] };
    thd_dat   inside { [I2C_MIN_TIMING : I2C_MAX_TIMING] };
    t_timeout inside { [I2C_MIN_TIMING : I2C_MAX_TIMING] };
    e_timeout inside { [0 : I2C_TIMEOUT_ENB] };

    solve t_r, tsu_dat, thd_dat before tlow;
    solve t_r                   before t_buf;
    if (force_use_incorrect_config) {
      // force derived timing parameters to be negative (incorrect DUT config)
      tsu_sta == t_r + t_buf + 1;  // negative tHoldStop
      tlow    == 2;                // negative tClockLow
      t_buf   == 2;
    } else {
      tsu_sta   inside { [I2C_MIN_TIMING : I2C_MAX_TIMING] };
      // force derived timing parameters to be positive (correct DUT config)
      tlow     inside { [(t_r + tsu_dat + thd_dat + 1) :
                         (t_r + tsu_dat + thd_dat + 1) + I2C_TIME_RANGE] };
      t_buf    inside { [(tsu_sta - t_r + 1) :
                         (tsu_sta - t_r + 1) + I2C_TIME_RANGE] };
    }
  }

  constraint num_wr_bytes_c {
    num_wr_bytes dist {
      1      :/ 2,
      [2:5]  :/ 5,
      [6:9]  :/ 5,
      [9:12] :/ 2
    };
  }
  constraint num_rd_bytes_c {
    num_rd_bytes dist {
      0      :/ 1,
      1      :/ 2,
      [2:5]  :/ 5,
      [6:9]  :/ 5,
      [9:12] :/ 2
    };
  }
  constraint en_intr_c {
    en_intr inside {[0: ((1 << NumI2cIntr) - 1)]};
  }
  constraint fmt_fifo_access_dly_c {
    fmt_fifo_access_dly inside {[1:5]};
  }
  constraint rx_fifo_access_dly_c {
    rx_fifo_access_dly inside {[1:5]};
  }

  `uvm_object_new

  virtual task device_init();
    i2c_device_seq m_dev_seq;

    m_dev_seq = i2c_device_seq::type_id::create("m_dev_seq");
    `uvm_info(`gfn, "start i2c_device sequence", UVM_DEBUG)
    fork
      m_dev_seq.start(p_sequencer.i2c_sequencer_h);
    join_none
  endtask : device_init

  virtual task host_init();
    `uvm_info(`gfn, "initialize i2c host registers", UVM_DEBUG)
    ral.ctrl.enablehost.set(1'b1);
    csr_update(ral.ctrl);
    if (do_interrupt) begin
      ral.intr_enable.set(en_intr);
      csr_update(ral.intr_enable);
      `DV_CHECK_RANDOMIZE_WITH_FATAL(ral.fifo_ctrl.rxilvl, value <= 4;)
      `DV_CHECK_RANDOMIZE_FATAL(ral.fifo_ctrl.fmtilvl)
      csr_update(ral.fifo_ctrl);
    end
  endtask : host_init

  function automatic void get_timing_values();
    // derived timing parameters
    timing_cfg.enbTimeOut  = e_timeout;
    timing_cfg.tTimeOut    = t_timeout;
    timing_cfg.tSetupStart = t_r + tsu_sta;
    timing_cfg.tHoldStart  = t_f + thd_sta;
    timing_cfg.tClockStart = thd_dat;
    timing_cfg.tClockLow   = tlow - t_r - tsu_dat - thd_dat;
    timing_cfg.tSetupBit   = t_r + tsu_dat;
    timing_cfg.tClockPulse = t_r + thigh + t_f;
    timing_cfg.tHoldBit    = t_f + thd_dat;
    timing_cfg.tClockStop  = t_f + tlow - thd_dat;
    timing_cfg.tSetupStop  = t_r + tsu_sto;
    timing_cfg.tHoldStop   = t_r + t_buf - tsu_sta;
    // ensure these parameter must be greater than zeros
    if (!force_use_incorrect_config) begin
      `DV_CHECK_GT_FATAL(timing_cfg.tClockLow, 0)
      `DV_CHECK_GT_FATAL(timing_cfg.tClockStop, 0)
      `DV_CHECK_GT_FATAL(timing_cfg.tHoldStop, 0)
    end
  endfunction : get_timing_values

  virtual task program_timing_regs();
    csr_wr(.csr(ral.timing0), .value({tlow, thigh}));
    csr_wr(.csr(ral.timing1), .value({t_f, t_r}));
    csr_wr(.csr(ral.timing2), .value({thd_sta, tsu_sta}));
    csr_wr(.csr(ral.timing3), .value({thd_dat, tsu_dat}));
    csr_wr(.csr(ral.timing4), .value({t_buf,   tsu_sto}));
    csr_wr(.csr(ral.timeout_ctrl), .value({e_timeout, t_timeout}));
    // configure i2c_agent_cfg
    cfg.m_i2c_agent_cfg.timing_cfg = timing_cfg;
    // set time to stop test
    cfg.m_i2c_agent_cfg.ok_to_end_delay_ns = DELAY_FOR_EOT_NS;
  endtask : program_timing_regs

  virtual task program_format_flag(i2c_item item, string msg="");
    bit [TL_DW-1:0] reg_val;

    csr_spinwait(.ptr(ral.status.fmtfull), .exp_data(1'b0));
    reg_val = {19'd0, item.nakok, item.rcont, item.read, item.stop, item.start, item.fbyte};
    csr_wr(.csr(ral.fdata), .value(reg_val));
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(fmt_fifo_access_dly)
    cfg.m_i2c_agent_cfg.vif.wait_for_dly(fmt_fifo_access_dly);
    print_format_flag(item, msg);
  endtask : program_format_flag

  task print_format_flag(i2c_item item, string msg="");
    string str;

    str = {str, $sformatf("\n%s, format flags 0x%h \n", msg,
                {item.nakok, item.rcont, item.read, item.stop, item.start, item.fbyte})};
    if (item.start) begin
      str = {str, $sformatf("  | %5s | %5s | %5s | %5s | %5s | %8s | %3s |\n",
          "nakok", "rcont", "read", "stop", "start", "addr", "r/w")};
      str = {str, $sformatf("  | %5d | %5d | %5d | %5d | %5d | %8x | %3s |",
          item.nakok, item.rcont, item.read, item.stop, item.start, item.fbyte[7:1],
          (item.fbyte[0]) ? "R" : "W")};
    end else begin
      str = {str, $sformatf("  | %5s | %5s | %5s | %5s | %5s | %8s |\n",
          "nakok", "rcont", "read", "stop", "start", "fbyte")};
      str = {str, $sformatf("  | %5d | %5d | %5d | %5d | %5d | %8x |",
          item.nakok, item.rcont, item.read, item.stop, item.start, item.fbyte)};
    end
    `uvm_info(`gfn, $sformatf("%s", str), UVM_DEBUG)
  endtask : print_format_flag

  //*******************************************
  // TODO: below functions/tasks
  //*******************************************
  virtual task clear_all_interrupts();
    bit [TL_DW-1:0] data;

    foreach (intr_state_csrs[i]) begin
      csr_rd(.ptr(intr_state_csrs[i]), .value(data));
      `uvm_info(`gfn, $sformatf("%s 0x%08h", intr_state_csrs[i].get_name(), data), UVM_DEBUG)
      if (data != 0) begin
        csr_wr(.csr(intr_state_csrs[i]), .value(data));
        csr_rd(.ptr(intr_state_csrs[i]), .value(data));
        // TODO: check the initial value fmt_watermark interrupt in/out of reset
        //`DV_CHECK_EQ(data, 0)
      end
    end
    // TODO:
    //`DV_CHECK_EQ(cfg.intr_vif.sample(), {NUM_MAX_INTERRUPTS{1'b0}})
  endtask : clear_all_interrupts
endclass : i2c_base_vseq
