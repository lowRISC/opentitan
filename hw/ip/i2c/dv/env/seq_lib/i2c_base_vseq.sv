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
  bit                         program_incorrect_regs = 1'b0;

  local timing_cfg_t          timing_cfg;
  bit [7:0]                   rd_data;
  i2c_item                    fmt_item;

  // random property
  rand uint                   fmt_fifo_access_dly;
  rand uint                   rx_fifo_access_dly;
  rand uint                   clear_intr_dly;

  rand uint                   num_runs;
  rand uint                   num_wr_bytes;
  rand uint                   num_rd_bytes;
  rand uint                   num_data_ovf;
  rand bit                    rw_bit;
  rand bit   [7:0]            wr_data[$];
  rand bit   [9:0]            addr;  // support both 7-bit and 10-bit target address
  rand bit   [2:0]            rxilvl;
  rand bit   [1:0]            fmtilvl;

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
  rand uint                   t_sda_unstable;     // sda unstable time during the posedge_clock
  rand uint                   t_sda_interference; // sda interference time during the posedge_clock
  rand uint                   t_scl_interference; // scl interference time during the posedge_clock

  // error intrs probability
  rand uint                   prob_sda_unstable;
  rand uint                   prob_sda_interference;
  rand uint                   prob_scl_interference;

  // constraints
  constraint addr_c {
    addr inside {[cfg.seq_cfg.i2c_min_addr : cfg.seq_cfg.i2c_max_addr]};
  }
  constraint fmtilvl_c {
    fmtilvl inside {[0 : cfg.seq_cfg.i2c_max_fmtilvl]};
  }
  constraint num_trans_c {
    num_trans inside {[cfg.seq_cfg.i2c_min_num_trans : cfg.seq_cfg.i2c_max_num_trans]};
  }
  constraint num_runs_c {
    num_runs inside {[cfg.seq_cfg.i2c_min_num_runs : cfg.seq_cfg.i2c_max_num_runs]};
  }

  // get an array with unique write data
  constraint wr_data_c {
    solve num_wr_bytes before wr_data;
    wr_data.size == num_wr_bytes;
    unique { wr_data };
  }

  // number of extra data write written to fmt to trigger interrupts
  // i.e. overflow, watermark
  constraint num_data_ovf_c {
    num_data_ovf inside {[I2C_RX_FIFO_DEPTH/4 : I2C_RX_FIFO_DEPTH/2]};
  }

  // create uniform assertion distributions of rx_watermark interrupt
  constraint rxilvl_c {
    rxilvl dist {
      [0:4] :/ 5,
      [5:cfg.seq_cfg.i2c_max_rxilvl] :/ 1
    };
  }
  constraint num_wr_bytes_c {
    num_wr_bytes dist {
      1       :/ 2,
      [2:4]   :/ 2,
      [5:8]   :/ 2,
      [9:31]  :/ 1,
      32      :/ 1
    };
  }
  constraint num_rd_bytes_c {
    num_rd_bytes < 256;
    num_rd_bytes dist {
      1       :/ 2,
      [2:4]   :/ 2,
      [5:8]   :/ 2,
      [9:16]  :/ 1,
      [17:31] :/ 1,
      32      :/ 1
    };
  }

  // use this prob_dist value to make interrupt assertion more discrepancy
  constraint prob_error_intr_c {
    prob_sda_unstable     dist {0 :/ (100 - cfg.seq_cfg.i2c_prob_sda_unstable),
                                1 :/ cfg.seq_cfg.i2c_prob_sda_unstable};
    prob_sda_interference dist {0 :/ (100 - cfg.seq_cfg.i2c_prob_sda_interference),
                                1 :/ cfg.seq_cfg.i2c_prob_sda_interference};
    prob_scl_interference dist {0 :/ (100 - cfg.seq_cfg.i2c_prob_scl_interference),
                                1 :/ cfg.seq_cfg.i2c_prob_scl_interference};
  }

  // contraints for fifo access delay
  constraint clear_intr_dly_c {
    clear_intr_dly inside {[cfg.seq_cfg.i2c_min_dly : cfg.seq_cfg.i2c_max_dly]};
  }
  constraint fmt_fifo_access_dly_c {
    fmt_fifo_access_dly inside {[cfg.seq_cfg.i2c_min_dly : cfg.seq_cfg.i2c_max_dly]};
  }
  constraint rx_fifo_access_dly_c {
    rx_fifo_access_dly inside {[cfg.seq_cfg.i2c_min_dly : cfg.seq_cfg.i2c_max_dly]};
  }

  // constraints for i2c timing registers
  constraint t_timeout_c {
    t_timeout inside {[cfg.seq_cfg.i2c_min_timing : cfg.seq_cfg.i2c_max_timing]};
  }

  constraint timing_val_c {
    thigh   inside {[cfg.seq_cfg.i2c_min_timing : cfg.seq_cfg.i2c_max_timing]};
    t_r     inside {[cfg.seq_cfg.i2c_min_timing : cfg.seq_cfg.i2c_max_timing]};
    t_f     inside {[cfg.seq_cfg.i2c_min_timing : cfg.seq_cfg.i2c_max_timing]};
    thd_sta inside {[cfg.seq_cfg.i2c_min_timing : cfg.seq_cfg.i2c_max_timing]};
    tsu_sto inside {[cfg.seq_cfg.i2c_min_timing : cfg.seq_cfg.i2c_max_timing]};
    tsu_dat inside {[cfg.seq_cfg.i2c_min_timing : cfg.seq_cfg.i2c_max_timing]};
    thd_dat inside {[cfg.seq_cfg.i2c_min_timing : cfg.seq_cfg.i2c_max_timing]};

    solve t_r, tsu_dat, thd_dat before tlow;
    solve t_r                   before t_buf;
    solve t_f, thigh            before t_sda_unstable, t_sda_interference;
    if (program_incorrect_regs) {
      // force derived timing parameters to be negative (incorrect DUT config)
      tsu_sta == t_r + t_buf + 1;  // negative tHoldStop
      tlow    == 2;                // negative tClockLow
      t_buf   == 2;
      t_sda_unstable     == 0;
      t_sda_interference == 0;
      t_scl_interference == 0;
    } else {
      tsu_sta inside {[cfg.seq_cfg.i2c_min_timing : cfg.seq_cfg.i2c_max_timing]};
      // force derived timing parameters to be positive (correct DUT config)
      tlow    inside {[(t_r + tsu_dat + thd_dat + 1) :
                       (t_r + tsu_dat + thd_dat + 1) + cfg.seq_cfg.i2c_time_range]};
      t_buf   inside {[(tsu_sta - t_r + 1) :
                       (tsu_sta - t_r + 1) + cfg.seq_cfg.i2c_time_range]};
      t_sda_unstable     inside {[0 : t_r + thigh + t_f - 1]};
      t_sda_interference inside {[0 : t_r + thigh + t_f - 1]};
      t_scl_interference inside {[0 : t_r + thigh + t_f - 1]};
    }
  }

  `uvm_object_new

  virtual task pre_start();
    cfg.reset_seq_cfg();
    // sync monitor and scoreboard setting
    cfg.m_i2c_agent_cfg.en_monitor = cfg.en_scb;
    `uvm_info(`gfn, $sformatf("\n  %s monitor and scoreboard",
        cfg.en_scb ? "enable" : "disable"), UVM_DEBUG)
    num_runs.rand_mode(0);
    num_trans_c.constraint_mode(0);
    super.pre_start();
  endtask : pre_start

  virtual task post_start();
    // env_cfg must be reset after vseq completion
    cfg.reset_seq_cfg();
    super.post_start();
    print_seq_cfg_vars("post-start");
  endtask : post_start

  virtual task initialization();
    wait(cfg.m_i2c_agent_cfg.vif.rst_ni);
    device_init();
    host_init();
    `uvm_info(`gfn, "\n  initialization is done", UVM_DEBUG)
  endtask : initialization

  virtual task device_init();
    i2c_device_seq m_dev_seq;

    m_dev_seq = i2c_device_seq::type_id::create("m_dev_seq");
    `uvm_info(`gfn, "\n  start i2c_device sequence", UVM_DEBUG)
    fork
      m_dev_seq.start(p_sequencer.i2c_sequencer_h);
    join_none
  endtask : device_init

  virtual task host_init();
    bit [TL_DW-1:0] intr_state;

    `uvm_info(`gfn, "\n  initialize host", UVM_DEBUG)
    // enable host/target
    ral.ctrl.enablehost.set(1'b1);
    ral.ctrl.enabletarget.set(1'b0);
    csr_update(ral.ctrl);

    // diable override
    ral.ovrd.txovrden.set(1'b0);
    csr_update(ral.ovrd);

    // clear fifos
    ral.fifo_ctrl.rxrst.set(1'b1);
    ral.fifo_ctrl.fmtrst.set(1'b1);
    csr_update(ral.fifo_ctrl);

    //enable then clear interrupts
    csr_wr(.csr(ral.intr_enable), .value({TL_DW{1'b1}}));
    process_interrupts();
  endtask : host_init

  virtual task wait_for_reprogram_registers();
    bit fmtempty, hostidle;
    bit [TL_DW-1:0] reg_val;

    do begin
      if (cfg.under_reset) break;
      csr_rd(.ptr(ral.status), .value(reg_val));
      fmtempty = bit'(get_field_val(ral.status.fmtempty, reg_val));
      hostidle = bit'(get_field_val(ral.status.hostidle, reg_val));
    end while (!fmtempty || !hostidle);
    `uvm_info(`gfn, $sformatf("\n  registers can be reprogrammed"), UVM_DEBUG);
  endtask : wait_for_reprogram_registers

  virtual task wait_host_for_idle();
    bit fmtempty, hostidle, rxempty;
    bit [TL_DW-1:0] reg_val;

    do begin
      if (cfg.under_reset) break;
      csr_rd(.ptr(ral.status), .value(reg_val));
      fmtempty = bit'(get_field_val(ral.status.fmtempty, reg_val));
      rxempty  = bit'(get_field_val(ral.status.rxempty, reg_val));
      hostidle = bit'(get_field_val(ral.status.hostidle, reg_val));
    end while (!fmtempty || !hostidle || !rxempty);
    `uvm_info(`gfn, $sformatf("\n  host is in idle state"), UVM_DEBUG);
  endtask : wait_host_for_idle

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

    // control interference and unstable interrupts
    timing_cfg.tSclInterference = (cfg.seq_cfg.en_scl_interference) ?
                                  prob_scl_interference * t_scl_interference : 0;
    timing_cfg.tSdaInterference = (cfg.seq_cfg.en_sda_interference) ?
                                  prob_sda_interference * t_sda_interference : 0;
    timing_cfg.tSdaUnstable     = (cfg.seq_cfg.en_sda_unstable) ?
                                  prob_sda_unstable * t_sda_unstable : 0;
    `uvm_info(`gfn, $sformatf("\n  tSclItf = %0d, tSdaItf = %0d, tSdaUnstable = %0d",
        timing_cfg.tSclInterference,
        timing_cfg.tSdaInterference,
        timing_cfg.tSdaUnstable), UVM_DEBUG)
    // ensure these parameter must be greater than zeros
    if (!program_incorrect_regs) begin
      `DV_CHECK_GT_FATAL(timing_cfg.tClockLow, 0)
      `DV_CHECK_GT_FATAL(timing_cfg.tClockStop, 0)
      `DV_CHECK_GT_FATAL(timing_cfg.tHoldStop, 0)
    end
  endfunction : get_timing_values

  virtual task program_registers();
    //*** program timing register
    ral.timing0.tlow.set(tlow);
    ral.timing0.thigh.set(thigh);
    csr_update(.csr(ral.timing0));
    ral.timing1.t_f.set(t_f);
    ral.timing1.t_r.set(t_r);
    csr_update(.csr(ral.timing1));
    ral.timing2.thd_sta.set(thd_sta);
    ral.timing2.tsu_sta.set(tsu_sta);
    csr_update(.csr(ral.timing2));
    ral.timing3.thd_dat.set(thd_dat);
    ral.timing3.tsu_dat.set(tsu_dat);
    csr_update(.csr(ral.timing3));
    ral.timing4.tsu_sto.set(tsu_sto);
    ral.timing4.t_buf.set(t_buf);
    csr_update(.csr(ral.timing4));
    ral.timeout_ctrl.en.set(e_timeout);
    ral.timeout_ctrl.val.set(t_timeout);
    csr_update(.csr(ral.timeout_ctrl));
    // configure i2c_agent_cfg
    cfg.m_i2c_agent_cfg.timing_cfg = timing_cfg;
    `uvm_info(`gfn, $sformatf("\n  cfg.m_i2c_agent_cfg.timing_cfg\n%p",
        cfg.m_i2c_agent_cfg.timing_cfg), UVM_DEBUG)
    // set time to stop test
    cfg.m_i2c_agent_cfg.ok_to_end_delay_ns = cfg.ok_to_end_delay_ns;
    // config target address mode of agent to the same
    cfg.m_i2c_agent_cfg.target_addr_mode = cfg.target_addr_mode;

    //*** program ilvl
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(fmtilvl)
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(rxilvl)
    ral.fifo_ctrl.rxilvl.set(rxilvl);
    ral.fifo_ctrl.fmtilvl.set(fmtilvl);
    csr_update(ral.fifo_ctrl);
  endtask : program_registers

  virtual task program_format_flag(i2c_item item, string msg = "", bit do_print = 1'b0);
    bit fmtfull;

    ral.fdata.nakok.set(item.nakok);
    ral.fdata.rcont.set(item.rcont);
    ral.fdata.read.set(item.read);
    ral.fdata.stop.set(item.stop);
    ral.fdata.start.set(item.start);
    ral.fdata.fbyte.set(item.fbyte);
    // en_fmt_underflow is set to ensure no write data overflow with fmt_fifo
    // regardless en_fmt_underflow set/unset, the last data (consist of STOP bit) must be
    // pushed into fmt_fifo to safely complete transaction
    if (!cfg.seq_cfg.en_fmt_overflow || fmt_item.stop) begin
      csr_spinwait(.ptr(ral.status.fmtfull), .exp_data(1'b0));
    end
    // if fmt_overflow irq is triggered it must be cleared before new fmt data is programmed
    // otherwise, scoreboard can drop this data while fmt_fifo is not full
    wait(!cfg.intr_vif.pins[FmtOverflow]);
    // program fmt_fifo
    csr_update(.csr(ral.fdata));

    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(fmt_fifo_access_dly)
    cfg.clk_rst_vif.wait_clks(fmt_fifo_access_dly);
    print_format_flag(item, msg, do_print);
  endtask : program_format_flag

  // read interrupts and randomly clear interrupts if set
  virtual task process_interrupts();
    bit [TL_DW-1:0] intr_state, intr_clear;

    // read interrupt
    csr_rd(.ptr(ral.intr_state), .value(intr_state));
    // clear interrupt if it is set
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(intr_clear,
                                       foreach (intr_clear[i]) {
                                           intr_state[i] -> intr_clear[i] == 1;
                                       })

    if (bit'(get_field_val(ral.intr_state.fmt_watermark, intr_clear))) begin
      `uvm_info(`gfn, "\n  clearing fmt_watermark", UVM_DEBUG)
    end
    if (bit'(get_field_val(ral.intr_state.rx_watermark, intr_clear))) begin
      `uvm_info(`gfn, "\n  clearing rx_watermark", UVM_DEBUG)
    end

    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(clear_intr_dly)
    cfg.clk_rst_vif.wait_clks(clear_intr_dly);
    csr_wr(.csr(ral.intr_state), .value(intr_clear));
  endtask : process_interrupts

  virtual task clear_interrupt(i2c_intr_e intr, bit verify_clear = 1'b1);
    csr_wr(.csr(ral.intr_state), .value(1 << intr));
    if (verify_clear) wait(!cfg.intr_vif.pins[intr]);
  endtask : clear_interrupt

  virtual function void print_seq_cfg_vars(string msg = "", bit do_print = 1'b0);
    if (do_print) begin
      string str;
      str = {str, $sformatf("\n  %s, %s, i2c_seq_cfg", msg, get_name())};
      str = {str, $sformatf("\n    en_scb                %b", cfg.en_scb)};
      str = {str, $sformatf("\n    en_monitor            %b", cfg.m_i2c_agent_cfg.en_monitor)};
      str = {str, $sformatf("\n    do_apply_reset        %b", do_apply_reset)};
      str = {str, $sformatf("\n    en_fmt_overflow       %b", cfg.seq_cfg.en_fmt_overflow)};
      str = {str, $sformatf("\n    en_rx_overflow        %b", cfg.seq_cfg.en_rx_overflow)};
      str = {str, $sformatf("\n    en_rx_watermark       %b", cfg.seq_cfg.en_rx_watermark)};
      str = {str, $sformatf("\n    en_sda_unstable       %b", cfg.seq_cfg.en_sda_unstable)};
      str = {str, $sformatf("\n    en_scl_interference   %b", cfg.seq_cfg.en_scl_interference)};
      str = {str, $sformatf("\n    en_sda_interference   %b", cfg.seq_cfg.en_sda_interference)};
      `uvm_info(`gfn, $sformatf("%s", str), UVM_LOW)
    end
  endfunction : print_seq_cfg_vars

  virtual function print_format_flag(i2c_item item, string msg = "", bit do_print = 1'b0);
    if (do_print) begin
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
      `uvm_info(`gfn, $sformatf("%s", str), UVM_LOW)
    end
  endfunction : print_format_flag

  virtual function void bound_check(bit [TL_DW-1:0] x, uint low_bound, uint high_bound);
    // check low_bound <= x <= high_bound
    `DV_CHECK_GE(high_bound, low_bound);
    `DV_CHECK_GE(x, low_bound);
    `DV_CHECK_LE(x, high_bound);
  endfunction : bound_check

endclass : i2c_base_vseq
