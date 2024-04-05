// Copyright lowRISC contributors (OpenTitan project).
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
  rand bit                    rw_bit; // 0 write, 1 read
  rand bit   [9:0]            addr;  // support both 7-bit and 10-bit target address
  rand bit   [6:0]            target_addr0;  // Target Address 0
  rand bit   [6:0]            target_addr1;  // Target Address 1
  rand bit   [6:0]            illegal_addr;  // Illegal target address

  rand bit   [7:0]            txdata;
  rand bit   [7:0]            rx_thresh;
  rand bit   [7:0]            fmt_thresh;
  rand bit   [7:0]            acq_thresh;
  rand bit   [7:0]            tx_thresh;

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

  // host timeout ctrl value
  bit [31:0]                  host_timeout_ctrl = 32'hffff;
  // Start counter including restart. Starting from 1 to match rtl value
  // and easy to trace.
  int start_cnt = 1;
  int read_rcvd[$];
  int full_txn_num = 0;
  int exp_rd_id = 0;
  int exp_wr_id = 0;

  // read_txn_q usage: a single byte of read data and only wdata is valid.
  i2c_item read_txn_q[$];
  int tran_id = 0;
  int sent_txn_cnt = 0;

  i2c_intr_e intr_q[$];
  bit expected_intr[i2c_intr_e];

  // Used for ack stop test
  bit [7:0] pre_feed_rd_data_q[$];
  int       pre_feed_cnt = 0;
  bit       read_ack_nack_q[$];
  bit       adjust_exp_read_byte = 0;

  // constraints
  constraint target_addr_c {
    solve target_addr0 before target_addr1;
    solve target_addr1 before illegal_addr;
    !(illegal_addr inside {target_addr0, target_addr1});
  }
  constraint addr_c {
    addr inside {[cfg.seq_cfg.i2c_min_addr : cfg.seq_cfg.i2c_max_addr]};
  }
  constraint fmt_thresh_c {
    // Interrupt is asserted when the level is _below_ the threshold
    fmt_thresh inside {[1 : cfg.seq_cfg.i2c_max_fmt_thresh]};
  }
  constraint txi_thresh_c {
    // Interrupt is asserted when the level is _below_ the threshold
    tx_thresh inside {[1 : cfg.seq_cfg.i2c_max_tx_thresh]};
  }
  constraint num_trans_c {
    num_trans inside {[cfg.seq_cfg.i2c_min_num_trans : cfg.seq_cfg.i2c_max_num_trans]};
  }
  constraint num_runs_c {
    num_runs inside {[cfg.seq_cfg.i2c_min_num_runs : cfg.seq_cfg.i2c_max_num_runs]};
  }

  // number of extra data write written to fmt to trigger interrupts
  // i.e. overflow, threshold
  constraint num_data_ovf_c {
    num_data_ovf inside {[I2C_RX_FIFO_DEPTH/4 : I2C_RX_FIFO_DEPTH/2]};
  }

  // create uniform assertion distributions of rx_threshold interrupt
  constraint rx_thresh_c {
    rx_thresh dist {
      [0:cfg.seq_cfg.i2c_max_rx_thresh] :/ cfg.seq_cfg.i2c_max_rx_thresh,
      [cfg.seq_cfg.i2c_max_rx_thresh+1:255] :/ 1
    };
  }
  // create uniform assertion distributions of acq_threshold interrupt
  constraint acq_thresh_c {
    acq_thresh dist {
      [0:cfg.seq_cfg.i2c_max_acq_thresh] :/ cfg.seq_cfg.i2c_max_acq_thresh,
      [cfg.seq_cfg.i2c_max_acq_thresh+1:255] :/ 1
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
    thigh   inside {[                         4 : cfg.seq_cfg.i2c_max_timing]};
    t_r     inside {[cfg.seq_cfg.i2c_min_timing : cfg.seq_cfg.i2c_max_timing]};
    t_f     inside {[cfg.seq_cfg.i2c_min_timing : cfg.seq_cfg.i2c_max_timing]};
    thd_sta inside {[cfg.seq_cfg.i2c_min_timing : cfg.seq_cfg.i2c_max_timing]};
    tsu_sto inside {[cfg.seq_cfg.i2c_min_timing : cfg.seq_cfg.i2c_max_timing]};
    tsu_dat inside {[cfg.seq_cfg.i2c_min_timing : cfg.seq_cfg.i2c_max_timing]};
    thd_dat inside {[cfg.seq_cfg.i2c_min_timing : cfg.seq_cfg.i2c_max_timing]};

    solve t_r, tsu_dat, thd_dat before tlow;
    solve t_r                   before t_buf;
    solve t_f, thigh            before t_sda_unstable, t_sda_interference;

    thd_sta > thd_dat + 1;
    t_buf > thd_dat + 1;

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
      // If we are generating a fixed_period SCL in the agent, we need the clock pulses
      // to be at-least long enough to contain an RSTART condition to chain transfers
      // together.
      thigh >= tsu_sta + t_f + thd_sta; // RSTART constraint
      // force derived timing parameters to be positive (correct DUT config)
      // tlow must be at least 2 greater than the sum of t_r + tsu_dat + thd_dat
      // because the flopped clock (see #15003 below) reduces tClockLow by 1.
      tlow    inside {[(t_r + tsu_dat + thd_dat + 2) :
                       (t_r + tsu_dat + thd_dat + 2) + cfg.seq_cfg.i2c_time_range]};
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

    // Initialize counters for stop_target_interrupt for stress_all test
    cfg.sent_acq_cnt = 0;
    cfg.rcvd_acq_cnt = 0;
    sent_txn_cnt = 0;
    cfg.m_i2c_agent_cfg.sent_rd_byte = 0;
    cfg.m_i2c_agent_cfg.rcvd_rd_byte = 0;
    host_timeout_ctrl = 32'hffff;
    cfg.m_i2c_agent_cfg.allow_ack_stop = 0;
    expected_intr.delete();

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
    // Use if_mode variable in agent_cfg as it is set in test
    if (cfg.m_i2c_agent_cfg.if_mode == Host) begin
      i2c_init(Device);
      agent_init(Host);
      `uvm_info(`gfn, "\n  initialization is done, DUT/AGENT = Target/Host", UVM_LOW)
    end else begin
      i2c_init(Host);
      agent_init(Device);
      `uvm_info(`gfn, "\n  initialization is done, DUT/AGENT = Host/Target", UVM_LOW)
    end

  endtask : initialization

  // 'cfg.m_i2c_agent_cfg.if_mode' is set by plusarg.
  // default value of if_mode in block level is 'Device'
  virtual task agent_init(if_mode_e mode = Device);
    i2c_base_seq m_base_seq;

    `uvm_info(`gfn, $sformatf("\n  initialize agent in mode %s", mode.name()), UVM_DEBUG)
    if (mode == Device) begin
      m_base_seq = i2c_base_seq::type_id::create("m_base_seq");
      `uvm_info(`gfn, $sformatf("\n  start i2c_sequence %s",
          cfg.m_i2c_agent_cfg.if_mode.name()), UVM_DEBUG)
      fork
        m_base_seq.start(p_sequencer.i2c_sequencer_h);
      join_none
    end
  endtask : agent_init

  virtual task i2c_init(if_mode_e mode = Host);
    bit [TL_DW-1:0] intr_state;

    `uvm_info(`gfn, $sformatf("\n  initialize host in mode %s", mode.name()), UVM_DEBUG)
    if (mode == Host) begin
      ral.ctrl.enablehost.set(1'b1);
      ral.ctrl.enabletarget.set(1'b0);
      ral.ctrl.llpbk.set(1'b0);
      csr_update(ral.ctrl);
      // diable override
      ral.ovrd.txovrden.set(1'b0);
      csr_update(ral.ovrd);
    end else begin
      ral.ctrl.enablehost.set(1'b0);
      ral.ctrl.enabletarget.set(1'b1);
      ral.ctrl.llpbk.set(1'b0);
      csr_update(ral.ctrl);
      ral.target_id.address0.set(target_addr0);
      ral.target_id.mask0.set(7'h7f);
      ral.target_id.address1.set(target_addr1);
      ral.target_id.mask1.set(7'h7f);
      csr_update(ral.target_id);
      // Host timeout control
      ral.host_timeout_ctrl.set(this.host_timeout_ctrl);
      csr_update(ral.host_timeout_ctrl);
      print_time_property();
      get_timing_values();
      program_registers();
    end

    // clear fifos
    ral.fifo_ctrl.rxrst.set(1'b1);
    ral.fifo_ctrl.fmtrst.set(1'b1);
    ral.fifo_ctrl.acqrst.set(1'b1);
    ral.fifo_ctrl.txrst.set(1'b1);
    csr_update(ral.fifo_ctrl);

    //enable then clear interrupts
    csr_wr(.ptr(ral.intr_enable), .value({TL_DW{1'b1}}));
    process_interrupts();
  endtask : i2c_init

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

  virtual task wait_for_target_idle();
    bit acqempty, targetidle;
    bit [TL_DW-1:0] reg_val;

    do begin
      if (cfg.under_reset) break;
      csr_rd(.ptr(ral.status), .value(reg_val));
      acqempty = bit'(get_field_val(ral.status.acqempty, reg_val));
      targetidle = bit'(get_field_val(ral.status.targetidle, reg_val));
    end while (!acqempty || !targetidle);
    `uvm_info(`gfn, $sformatf("\n  target is in idle state"), UVM_DEBUG);
  endtask : wait_for_target_idle

  function automatic void get_timing_values();
    // derived timing parameters
    timing_cfg.enbTimeOut  = e_timeout;
    timing_cfg.tTimeOut    = t_timeout;
    timing_cfg.tSetupStart = t_r + tsu_sta;
    timing_cfg.tHoldStart  = t_f + thd_sta;
    timing_cfg.tClockStart = thd_dat;
    // An extra -1 is added to tClokLow because scl coming from the host side is now flopped.
    // See #15003
    // This means, relative to the expectation of the DUT, we have "1 less" cycle of clock
    // time.  Specifically, if the DUT drives the clock at cycle 1, the device does not see
    // the clock until cycle 2.  This means, the device expectation of how long "low" is
    // now shrunk by 1, since the end point is still fixed.
    timing_cfg.tClockLow   = tlow - t_r - tsu_dat - thd_dat - 1;
    timing_cfg.tSetupBit   = t_r + tsu_dat;
    timing_cfg.tClockPulse = t_r + thigh;
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
        cfg.m_i2c_agent_cfg.timing_cfg), UVM_MEDIUM)

    //*** program Host mode FIFO thresholds
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(rx_thresh)
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(fmt_thresh)
    ral.host_fifo_config.rx_thresh.set(rx_thresh);
    ral.host_fifo_config.fmt_thresh.set(fmt_thresh);
    csr_update(ral.host_fifo_config);
    //*** program Target mode FIFO thresholds
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(acq_thresh)
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(tx_thresh)
    ral.target_fifo_config.acq_thresh.set(acq_thresh);
    ral.target_fifo_config.tx_thresh.set(tx_thresh);
    csr_update(ral.target_fifo_config);
    //*** set FIFO_CTRL register
    csr_update(ral.fifo_ctrl);
  endtask : program_registers

  virtual task program_format_flag(i2c_item item, string msg = "", bit do_print = 1'b0);
    bit fmtfull;

    ral.fdata.nakok.set(item.nakok);
    ral.fdata.rcont.set(item.rcont);
    ral.fdata.readb.set(item.read);
    ral.fdata.stop.set(item.stop);
    ral.fdata.start.set(item.start);
    ral.fdata.fbyte.set(item.fbyte);
    csr_spinwait(.ptr(ral.status.fmtfull), .exp_data(1'b0));
    // program fmt_fifo
    csr_update(.csr(ral.fdata));

    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(fmt_fifo_access_dly)
    cfg.clk_rst_vif.wait_clks(fmt_fifo_access_dly);
    print_format_flag(item, msg, do_print);
  endtask : program_format_flag

  // Read and clear interrupts
  //
  // - Clear all interrupts that are active
  // - Add a delay of 'clear_intr_dly' cycles before the W1C operation
  // - If 'nak' irq is active, add an extra delay of 1000 cycles
  virtual task process_interrupts();
    bit [TL_DW-1:0] intr_state, intr_clear;

    // read interrupt
    csr_rd(.ptr(ral.intr_state), .value(intr_state));
    // clear interrupt if it is set
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(intr_clear,
                                       foreach (intr_clear[i]) {
                                           intr_state[i] -> intr_clear[i] == 1;
                                       })
    // TODO: It is NOT possible to clear this interrupt by a simple INTR_STATE write now!
    if (bit'(get_field_val(ral.intr_state.fmt_threshold, intr_clear))) begin
      `uvm_info(`gfn, "\n  clearing fmt_threshold", UVM_DEBUG)
    end
    // TODO: It is NOT possible to clear this interrupt by a simple INTR_STATE write now!
    if (bit'(get_field_val(ral.intr_state.rx_threshold, intr_clear))) begin
      `uvm_info(`gfn, "\n  clearing rx_threshold", UVM_DEBUG)
    end
    if (bit'(get_field_val(ral.intr_state.stretch_timeout, intr_clear))) begin
      `uvm_info(`gfn, "\n  clearing stretch_timeout", UVM_DEBUG)
    end
    if (bit'(get_field_val(ral.intr_state.tx_stretch, intr_clear))) begin
      `uvm_info(`gfn, "\n  clearing tx_stretch", UVM_DEBUG)
    end
    if (bit'(get_field_val(ral.intr_state.controller_halt, intr_clear))) begin
      // Add a longer delay to mimic a software handler clearing the NAK condition
      cfg.clk_rst_vif.wait_clks(1_000);
      `uvm_info(`gfn, "Clearing 'NAK' interrupt, allowing FSM to continue...", UVM_DEBUG)
      csr_wr(.ptr(ral.controller_events.nack), .value(1));
    end

    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(clear_intr_dly)
    cfg.clk_rst_vif.wait_clks(clear_intr_dly);
    csr_wr(.ptr(ral.intr_state), .value(intr_clear));
  endtask : process_interrupts

  virtual task clear_interrupt(i2c_intr_e intr, bit verify_clear = 1'b1);
    csr_wr(.ptr(ral.intr_state), .value(1 << intr));
    if (verify_clear) wait(!cfg.intr_vif.pins[intr]);
  endtask : clear_interrupt

  virtual function void print_seq_cfg_vars(string msg = "", bit do_print = 1'b0);
    if (do_print) begin
      string str;
      str = {str, $sformatf("\n  %s, %s, i2c_seq_cfg", msg, get_name())};
      str = {str, $sformatf("\n    en_scb                %b", cfg.en_scb)};
      str = {str, $sformatf("\n    en_monitor            %b", cfg.m_i2c_agent_cfg.en_monitor)};
      str = {str, $sformatf("\n    do_apply_reset        %b", do_apply_reset)};
      str = {str, $sformatf("\n    en_rx_overflow        %b", cfg.seq_cfg.en_rx_overflow)};
      str = {str, $sformatf("\n    en_rx_threshold       %b", cfg.seq_cfg.en_rx_threshold)};
      str = {str, $sformatf("\n    en_sda_unstable       %b", cfg.seq_cfg.en_sda_unstable)};
      str = {str, $sformatf("\n    en_scl_interference   %b", cfg.seq_cfg.en_scl_interference)};
      str = {str, $sformatf("\n    en_sda_interference   %b", cfg.seq_cfg.en_sda_interference)};
      `uvm_info(`gfn, $sformatf("%s", str), UVM_LOW)
    end
  endfunction : print_seq_cfg_vars

  virtual function void print_format_flag(i2c_item item, string msg = "", bit do_print = 1'b0);
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

  task reset_rx_fifo();
    csr_wr(.ptr(ral.fifo_ctrl.rxrst), .value(1'b1));
    csr_wr(.ptr(ral.fifo_ctrl.rxrst), .value(1'b0));
  endtask : reset_rx_fifo

  task reset_fmt_fifo();
    csr_wr(.ptr(ral.fifo_ctrl.fmtrst), .value(1'b1));
    csr_wr(.ptr(ral.fifo_ctrl.fmtrst), .value(1'b0));
  endtask : reset_fmt_fifo

  task program_tx_fifo(int tx_bytes);
    for (int i = 0; i < tx_bytes; i++) begin
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(txdata)
      csr_wr(.ptr(ral.txdata), .value(txdata));
    end
  endtask : program_tx_fifo

  task read_acqdata (int num_bytes);
    bit [6:0] acqlvl;
    bit [7:0] abyte;
    bit [1:0] signal;
    csr_rd_check(.ptr(ral.status.acqempty), .compare_value(0));
    csr_rd(.ptr(ral.target_fifo_status.acqlvl), .value(acqlvl));
    `DV_CHECK_EQ(acqlvl, (num_bytes+2)) // addr byte + data bytes + junk byte
    for (int i = 0; i < (num_bytes+2); i++) begin
      csr_rd(.ptr(ral.acqdata), .value({signal,abyte}));
    end
  endtask : read_acqdata

  // Use for debug only
  function void print_time_property();
    `uvm_info(`gfn, $sformatf("timing_prop"), UVM_MEDIUM)
    // high period of the SCL in clock units
    `uvm_info(`gfn, $sformatf("thigh:%0d", thigh), UVM_MEDIUM);
    // low period of the SCL in clock units
    `uvm_info(`gfn, $sformatf("tlow:%0d", tlow), UVM_MEDIUM);
    // rise time of both SDA and SCL in clock units
    `uvm_info(`gfn, $sformatf("t_r:%0d", t_r), UVM_MEDIUM);
    // fall time of both SDA and SCL in clock units
    `uvm_info(`gfn, $sformatf("t_f:%0d", t_f), UVM_MEDIUM);
    // hold time for (repeated) START in clock units
    `uvm_info(`gfn, $sformatf("thd_sta:%0d", thd_sta), UVM_MEDIUM);
    // setup time for repeated START in clock units
    `uvm_info(`gfn, $sformatf("tsu_sta:%0d", tsu_sta), UVM_MEDIUM);
    // setup time for STOP in clock units
    `uvm_info(`gfn, $sformatf("tsu_sto:%0d", tsu_sto), UVM_MEDIUM);
    // data setup time in clock units
    `uvm_info(`gfn, $sformatf("tsu_dat:%0d", tsu_dat), UVM_MEDIUM);
    // data hold time in clock units
    `uvm_info(`gfn, $sformatf("thd_dat:%0d", thd_dat), UVM_MEDIUM);
    // bus free time between STOP and START in clock units
    `uvm_info(`gfn, $sformatf("t_buf:%0d", t_buf), UVM_MEDIUM);
    // max time target may stretch the clock
    `uvm_info(`gfn, $sformatf("t_timeout:%0d", t_timeout), UVM_MEDIUM);
    // max time target may stretch the clock
    `uvm_info(`gfn, $sformatf("e_timeout:%0d", e_timeout), UVM_MEDIUM);
    // sda unstable time during the posedge_clock
    `uvm_info(`gfn, $sformatf("t_sda_unstable:%0d", t_sda_unstable), UVM_MEDIUM);
    // sda interference time during the posedge_clock
    `uvm_info(`gfn, $sformatf("t_sda_interference:%0d", t_sda_interference), UVM_MEDIUM);
    // scl interference time during the posedge_clock
    `uvm_info(`gfn, $sformatf("t_scl_interference:%0d", t_scl_interference), UVM_MEDIUM);
    `uvm_info(`gfn, $sformatf("error intrs probability"), UVM_MEDIUM)
    `uvm_info(`gfn, $sformatf("prob_sda_unstable:%0d    ", prob_sda_unstable), UVM_MEDIUM);
    `uvm_info(`gfn, $sformatf("prob_sda_interference:%0d", prob_sda_interference), UVM_MEDIUM);
    `uvm_info(`gfn, $sformatf("prob_scl_interference:%0d", prob_scl_interference), UVM_MEDIUM);
  endfunction

  // Print i2c_item.data_q with RS command notation
  function void print_wr_data(bit is_read, i2c_item myq[$]);
    int idx = 1;
    int rd_idx = 0;
    bit read = is_read;

    foreach (myq[i]) begin
      if (myq[i].rstart) begin
        if (cfg.m_i2c_agent_cfg.allow_ack_stop & read) begin
            `uvm_info("seq", $sformatf("(n)ack: %s", (read_ack_nack_q[rd_idx++]) ?
                                       "NACK" : "ACK"), UVM_MEDIUM)
        end
        read = myq[i].read;
        `uvm_info("seq", $sformatf("idx %0d RS rw:%0d", start_cnt++, myq[i].read), UVM_MEDIUM)
        idx = 1;
      end else begin
        `uvm_info("seq", $sformatf("%2d: 0x%2x", idx++, myq[i].wdata), UVM_MEDIUM)
      end
    end
    if (cfg.m_i2c_agent_cfg.allow_ack_stop & read) begin
      `uvm_info("seq", $sformatf("(n)ack: %s", (read_ack_nack_q[rd_idx]) ?
                                 "NACK" : "ACK"), UVM_MEDIUM)
    end
  endfunction

  // Update read data to send based on
  // pre written tx data and pre defined ack / nack status
  // Used only for ack stop test
  function void update_wr_data(bit is_read, ref i2c_item myq[$],
                               input bit force_ack);
    bit read = is_read;
    foreach (myq[i]) begin
      if (myq[i].rstart) begin
        // if previous segment is read, store ack/nack
        if (read) read_ack_nack_q.push_back($urandom_range(0 ,1));
        read = myq[i].read;
      end else begin
        if (read) begin
          if (pre_feed_rd_data_q.size > 0) begin
            myq[i].wdata = pre_feed_rd_data_q.pop_front();
          end
        end
      end
    end
    if (read) begin
      bit ack_nack = force_ack ? 0 : $urandom_range(0, 1);
      read_ack_nack_q.push_back(ack_nack);
    end
  endfunction // update_wr_data

  // Set rw bit based on cfg rd/wr pct
  function bit get_read_write();
    bit rw;
    randcase
      cfg.wr_pct: rw = 0;
      cfg.rd_pct: rw = 1;
    endcase
    return rw;
  endfunction // get_read_write

  // Call read_acq_fifo until send and rcv counter become the same.
  virtual task process_acq();
    int delay;
    bit acq_fifo_empty;
    bit read_one = 0;
    `DV_WAIT(cfg.sent_acq_cnt > 0,, cfg.spinwait_timeout_ns, "process_acq")

    while (cfg.sent_acq_cnt != cfg.rcvd_acq_cnt) begin
      if (cfg.slow_acq) begin
        delay = $urandom_range(50, 100);
        #(delay * 1us);
        read_one = 1;
      end
      read_acq_fifo(read_one, acq_fifo_empty);
    end
  endtask

  // Polling read_rcvd q and fetch read data to txdata fifo
  virtual task process_txq();
    `DV_WAIT(cfg.m_i2c_agent_cfg.sent_rd_byte > 0,, cfg.spinwait_timeout_ns, "process_txq")

    while (cfg.m_i2c_agent_cfg.sent_rd_byte != cfg.m_i2c_agent_cfg.rcvd_rd_byte ||
           sent_txn_cnt < num_trans) begin
      cfg.clk_rst_vif.wait_clks(1);
      write_tx_fifo(.add_delay(cfg.slow_txq));
    end
  endtask

  // Create byte transaction (payload) to read or write.
  // Restart can be stuffed in between bytes except first and the last bytes.
  // While normal transaction type (read, write) is decided in 'fetch_txn',
  // Restat transaction type is set here to make io trace easier.
  virtual function void create_txn(ref i2c_item myq[$]);
    bit [7:0] wdata_q[$];
    i2c_item  txn;
    bit       rs_avl;

    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(wdata_q,
                                       wdata_q.size() inside {
                           [cfg.min_data : cfg.max_data]};)

    for (int i = 0; i < wdata_q.size(); i++) begin
      if ($urandom_range(0,9) < cfg.rs_pct) rs_avl = 1;
      else rs_avl = 0;
      // restart entry
      if (rs_avl == 1 && wdata_q.size() > 1 &&
          i inside {[1:wdata_q.size() -1]}) begin
        `uvm_info("seq", $sformatf("RS inserted before data %0d", i), UVM_HIGH)
        `uvm_create_obj(i2c_item, txn)
        txn.drv_type = HostRStart;
        txn.rstart = 1;
        txn.stop = 0;
        txn.read = get_read_write();
        myq.push_back(txn);
      end
      `uvm_create_obj(i2c_item, txn)
      txn.drv_type = HostData;
      txn.wdata = wdata_q[i];
      myq.push_back(txn);
    end
  endfunction

  // Receive byte stream from 'create_txn' and forward to driver's request q,
  // with adding 'Start and Stop'.
  // Expected transaction is created in the task.
  // For write transaction and address transaction, expected transaction mimics acq read data.
  // For read transaction, all read bytes for one transaction is accumulated to 'full_txn'
  // and compared with received transaction at the scoreboard.
  virtual function void fetch_txn(ref i2c_item src_q[$], i2c_item dst_q[$],
                                  input bit force_ack = 0, bit skip_start = 0);
    // A temporary, representing each item that is pushed to the dst_q intended for the driver.
    i2c_item txn;
    i2c_item rs_txn;
    // The subset of items that address the DUT that are expected from the ACQ FIFO.
    i2c_item exp_txn;
    // All items to go on the bus, including those that don't address the DUT.
    i2c_item full_txn;
    int read_size;
    bit is_read = get_read_write();
    bit [6:0] t_addr;
    bit valid_addr;
    bit addressed;

    `uvm_info("seq", $sformatf("idx %0d:is_read:%0b size:%0d fetch_txn:%0d", start_cnt++, is_read,
                               src_q.size(), full_txn_num++), UVM_MEDIUM)
    // Update read data with pre filled one and ack/nack for ack stop test
    if (cfg.m_i2c_agent_cfg.allow_ack_stop) begin
      update_wr_data(is_read, src_q, force_ack);
    end

    print_wr_data(is_read, src_q);
    `uvm_create_obj(i2c_item, full_txn)

    // Add 'START' to the front
    if (!skip_start) begin
      `uvm_create_obj(i2c_item, txn)
      txn.drv_type = HostStart;
      dst_q.push_back(txn);
      full_txn.start = 1;
    end
    else begin
      full_txn.rstart = 1;
    end
    if (is_read) full_txn.tran_id = this.exp_rd_id;
    // Address
    `uvm_create_obj(i2c_item, txn)
    `uvm_create_obj(i2c_item, exp_txn)
    txn.drv_type = HostData;
    if (skip_start) begin
      txn.rstart = 1;
    end else begin
      txn.start = 1;
    end
    txn.wdata[7:1] = get_target_addr(); //target_addr0;
    txn.wdata[0] = is_read;
    valid_addr = is_target_addr(txn.wdata[7:1]);

    txn.tran_id = this.tran_id;
    `downcast(exp_txn, txn.clone());
    dst_q.push_back(txn);
    full_txn.addr = txn.wdata[7:1];
    full_txn.read = is_read;

    // Start command acq entry
    if (valid_addr) begin
      p_sequencer.target_mode_wr_exp_port.write(exp_txn);
      cfg.sent_acq_cnt++;
      this.tran_id++;
      if (is_read) this.exp_rd_id++;
      addressed = 1;
    end
    read_size = get_read_data_size(src_q, is_read, read_rcvd);
    cfg.m_i2c_agent_cfg.sent_rd_byte += read_size;
    // Data
    while (src_q.size() > 0) begin
      `uvm_create_obj(i2c_item, txn)
      txn = src_q.pop_front();
      if (txn.drv_type != HostRStart) begin
        // Restart only has empty data for address holder
        full_txn.data_q.push_back(txn.wdata);
      end

      if (txn.drv_type == HostRStart) begin
        bit prv_read = 0;
        bit prv_valid = valid_addr;

        `uvm_create_obj(i2c_item, rs_txn)
        `downcast(rs_txn, txn.clone())
        dst_q.push_back(txn);

        t_addr = get_target_addr();
        valid_addr = is_target_addr(t_addr);
        rs_txn.drv_type = HostData;
        rs_txn.start = 0;
        rs_txn.rstart = 1;
        rs_txn.wdata[7:1] = t_addr;
        prv_read = is_read;
        is_read = rs_txn.read;
        rs_txn.wdata[0] = is_read;
        dst_q.push_back(rs_txn);
        // create a separate stat/addr entry for exp
        `uvm_create_obj(i2c_item, exp_txn)
        `downcast(exp_txn, rs_txn.clone());
        exp_txn.tran_id = this.tran_id;


        addressed |= valid_addr;
        // Restart command entry
        if (valid_addr) begin
           p_sequencer.target_mode_wr_exp_port.write(exp_txn);
           cfg.sent_acq_cnt++;
           this.tran_id++;
        end
        // fetch previous full_txn and creat a new one
        if (prv_read) begin
          full_txn.stop = 1;
          if (prv_valid) p_sequencer.target_mode_rd_exp_port.write(full_txn);
        end
        `uvm_create_obj(i2c_item, full_txn)
        `downcast(full_txn, rs_txn);
        if (is_read) begin
          full_txn.tran_id = exp_rd_id;
          if (valid_addr) exp_rd_id++;
        end
      end else begin
        if (is_read) begin
          i2c_item read_txn;
          `uvm_create_obj(i2c_item, read_txn)
          `downcast(read_txn, txn.clone())
          full_txn.num_data++;
          if (src_q.size() == 0) begin
            txn.drv_type = get_ack_nack(.is_stop(1));
          end else begin
            // if your next item is restart Do nack
            if (src_q[0].drv_type == HostRStart) txn.drv_type = get_ack_nack();
            else txn.drv_type = HostAck;
          end
          dst_q.push_back(txn);
          read_txn_q.push_back(read_txn);
        end else begin
          `downcast(exp_txn, txn.clone());
          // Write payload
          dst_q.push_back(txn);
          if (valid_addr) begin
            exp_txn.tran_id = this.tran_id++;
            p_sequencer.target_mode_wr_exp_port.write(exp_txn);
            cfg.sent_acq_cnt++;
          end
        end
      end
    end // while (src_q.size() > 0)

    // Stop
    `uvm_create_obj(i2c_item, txn)
    `uvm_create_obj(i2c_item, exp_txn)
    txn.tran_id = this.tran_id;
    txn.stop = 1;
    txn.drv_type = HostStop;
    `downcast(exp_txn, txn.clone());
    dst_q.push_back(txn);
    full_txn.stop = 1;
    if (addressed) begin
       p_sequencer.target_mode_wr_exp_port.write(exp_txn);
       cfg.sent_acq_cnt++;
       this.tran_id++;
    end
    if (is_read) begin
      if (valid_addr) p_sequencer.target_mode_rd_exp_port.write(full_txn);
    end
  endfunction

  // Scan i2c_item q and count total byte of read data.
  // Also store read data per commmand to rcvd q.
  function int get_read_data_size(i2c_item myq[$], bit is_read, ref int rcvd[$]);
    int cnt = 0;
    int per_cmd_cnt = 0;

    for (int i = 0; i < myq.size(); i++) begin
      if (myq[i].rstart) is_read = myq[i].read;
      if (is_read & !myq[i].rstart) begin
        cnt++;
        per_cmd_cnt++;
      end else begin
        if (per_cmd_cnt > 0) begin
          rcvd.push_back(per_cmd_cnt);
          per_cmd_cnt = 0;
        end
      end
    end // for (int i = 0; i < myq.size(); i++)
    if (per_cmd_cnt > 0) begin
      rcvd.push_back(per_cmd_cnt);
      per_cmd_cnt = 0;
    end
    return cnt;
  endfunction

  // This task needs to set do_clear_all_interrupts = 0
  virtual task process_target_interrupts();
    int delay;
    bit acq_fifo_empty;
    bit read_one = 0;
    while (!cfg.stop_intr_handler) begin
      @(posedge cfg.clk_rst_vif.clk);
      if (cfg.intr_vif.pins[AcqFull]) begin
        if (cfg.slow_acq) begin
          acq_fifo_empty = 0;
          while (!acq_fifo_empty) begin
            delay = $urandom_range(50, 100);
            #(delay * 1us);
            read_acq_fifo(1, acq_fifo_empty);
          end
        end else begin
          read_acq_fifo(0, acq_fifo_empty);
        end
      end else if (cfg.intr_vif.pins[TxStretch]) begin
        proc_intr_txstretch();
      end else if (cfg.intr_vif.pins[CmdComplete]) begin
        proc_intr_cmdcomplete();
      end else if (cfg.read_all_acq_entries) begin
        read_acq_fifo(0, acq_fifo_empty);
      end else begin
        for (int i = 0; i < NumI2cIntr; i++) begin
          i2c_intr_e my_intr = i2c_intr_e'(i);
          if (!expected_intr.exists(my_intr)) begin
            if (cfg.intr_vif.pins[i] !== 0) begin
              `uvm_error("process_target_interrupts",
                         $sformatf("Unexpected interrupt is set %s", my_intr.name))
            end
          end
        end
      end // else: !if(cfg.intr_vif.pins[CmdComplete])
      // When bad command is dropped, expected rd_byte is adjust in 'write_tx_fifo'.
      // But for the last bad read command, we have to adjust expected rd_byte separately
      // because we will not call 'write_tx_fifo'.
      if (adjust_exp_read_byte == 1 &&
          cfg.sent_acq_cnt == cfg.rcvd_acq_cnt) begin
         int read_size;
         while (cfg.m_i2c_agent_cfg.read_addr_q.size > 0) begin
            read_size = read_rcvd.pop_front();
            if (!cfg.m_i2c_agent_cfg.read_addr_q.pop_front) begin
               repeat (read_size) void'(read_txn_q.pop_front());
               cfg.m_i2c_agent_cfg.sent_rd_byte -= read_size;
            end
         end
      end
    end
  endtask

  // Fill tx fifo for a single read transaction.
  task write_tx_fifo(bit add_delay = 0);
    uvm_reg_data_t data;
    int read_size;
    int rd_txfifo_timeout_ns = 10_000_000;
    // indefinite time
    int tx_empty_timeout_ns = 500_000_000;
    bit is_valid;

    string id = "write_tx_fifo";
    if (cfg.m_i2c_agent_cfg.allow_bad_addr) begin
       is_valid = cfg.m_i2c_agent_cfg.read_addr_q.pop_front();
       if (!is_valid) begin
          read_size = read_rcvd.pop_front();
          repeat (read_size) void'(read_txn_q.pop_front());
          cfg.m_i2c_agent_cfg.sent_rd_byte -= read_size;
          return;
       end
    end

    if (add_delay) id = {id, "_delay"};
    if (read_rcvd.size() > 0) begin
      read_size = read_rcvd.pop_front();
      `uvm_info(id, $sformatf("read_size :%0d", read_size), UVM_HIGH)
    end else begin
      // if ack stop test mode,
      // test need to feed 1 extraa tx fifo data at the end
      // to avoid dead lock
      if (cfg.m_i2c_agent_cfg.allow_ack_stop) begin
        `uvm_info(id, "feed extra ack/stop data", UVM_MEDIUM)
        csr_wr(.ptr(ral.txdata), .value('hff));
        pre_feed_rd_data_q.push_back(8'hff);
        pre_feed_cnt++;
      end
    end

    while (read_size > 0) begin
      cfg.clk_rst_vif.wait_clks(1);
      if (add_delay) begin
        if ($urandom_range(0, 1)) begin
          // Wait for txfifo to be empty before adding data,
          // this creates more stretching conditions.
          csr_spinwait(.ptr(ral.status.txempty), .exp_data(1'b1),
                       .timeout_ns(tx_empty_timeout_ns));
        end
      end
      if (read_txn_q.size() > 0) begin
        i2c_item item;
        // check tx fifo is full
        if (cfg.use_intr_handler) begin
          data = 1;
          // If tx_stretch interrupt is set,
          // interrupt handler in tb routine is to fill up tx fifo and empty acq fifo.
          // if tx fifo is alreay full, this routine can block 'read_acq_fifo'
          // and causes deadlock by waiting txempty forever.
          // So if interrupt handler is used, make each task not block the other
          while (data) begin
            bit is_empty;
            csr_rd(.ptr(ral.status.txfull), .value(data));
            // if tx fifo is full, real acq fifo to remove
            // tx_stretch condition
            if (data) begin
              read_acq_fifo(0, is_empty);
            end
          end

        end else begin
          csr_spinwait(.ptr(ral.status.txfull), .exp_data(1'b0),
                       .timeout_ns(rd_txfifo_timeout_ns));
        end
        `uvm_create_obj(i2c_item, item)
        item = read_txn_q.pop_front();
        `uvm_info(id, $sformatf("send rdata:%x", item.wdata), UVM_MEDIUM)

        // Send only there is no pre feed data
        if (pre_feed_cnt == 0) csr_wr(.ptr(ral.txdata), .value(item.wdata));
        else pre_feed_cnt--;

        read_size--;
      end
    end
  endtask

  // when read_one = 1. check acqempty and read a single entry
  // and return acq_fifo_empty.
  // When read_one = 0, read acq fifo up to acqlvl and convert read data
  // to i2c_item and send to wr_obs_port
  task read_acq_fifo(bit read_one, ref bit acq_fifo_empty);
    uvm_reg_data_t read_data;
    i2c_item obs;
    acq_fifo_empty = 0;
    if (read_one) begin
    // Polling if status.acqempty is zero and skip read fifo
    // if fifo is empty.
      csr_rd(.ptr(ral.status.acqempty), .value(acq_fifo_empty));
      read_data = (acq_fifo_empty)? 0 : 1;
    end else csr_rd(.ptr(ral.target_fifo_status.acqlvl), .value(read_data));

    repeat(read_data) begin
      // read one entry and compare
      csr_rd(.ptr(ral.acqdata), .value(read_data));
      `uvm_info("process_acq", $sformatf("acq data %x", read_data), UVM_MEDIUM)
      // Capture the same read data from 'process_tl_access' sb
      obs = acq2item(read_data);
    end

    if (read_data == 0) begin
      cfg.clk_rst_vif.wait_clks(1);
      `uvm_info("process_acq", $sformatf("acq_dbg: sent:%0d rcvd:%0d acq_is_empty",
                                         cfg.sent_acq_cnt, cfg.rcvd_acq_cnt), UVM_HIGH)
    end
  endtask // read_acq_fifo

  // is_stop: Whether the next symbol is to be a Stop
  function drv_type_e get_ack_nack(bit is_stop = 0);
    drv_type_e rsp = HostNAck;
    if (cfg.m_i2c_agent_cfg.allow_ack_stop) begin
      if (read_ack_nack_q.pop_front()) begin
        rsp = HostNAck;
      end else begin
        rsp = HostAck;
        if (is_stop) begin
          cfg.sent_ack_stop++;
        end
      end
    end
    return rsp;
  endfunction // get_ack_nack

  // Calling this task will trigger unexp_stop interrupt.
  task send_ack_stop();
    i2c_target_base_seq m_i2c_host_seq;
    i2c_item txn_q[$];
    cfg.rs_pct = 0;
    cfg.wr_pct = 0;

    `uvm_create_obj(i2c_target_base_seq, m_i2c_host_seq)
    create_txn(txn_q);
    fetch_txn(txn_q, m_i2c_host_seq.req_q, 1);
    m_i2c_host_seq.start(p_sequencer.i2c_sequencer_h);
    sent_txn_cnt++;
  endtask

  virtual task stop_target_interrupt_handler();
    string id = "stop_interrupt_handler";
    int   acq_rd_cyc;
    acq_rd_cyc = 9 * (thigh + tlow);
    `DV_WAIT(cfg.sent_acq_cnt > 0,, cfg.spinwait_timeout_ns, id)
    `DV_WAIT(sent_txn_cnt == num_trans,, cfg.long_spinwait_timeout_ns, id)
    cfg.read_all_acq_entries = 1;
    if (cfg.rd_pct != 0) begin
      `DV_WAIT(cfg.m_i2c_agent_cfg.sent_rd_byte > 0,, cfg.spinwait_timeout_ns, id)
      if (cfg.m_i2c_agent_cfg.allow_bad_addr) adjust_exp_read_byte = 1;

      `DV_WAIT(cfg.m_i2c_agent_cfg.sent_rd_byte == cfg.m_i2c_agent_cfg.rcvd_rd_byte,,
               cfg.long_spinwait_timeout_ns, id)
    end
    `DV_WAIT(cfg.sent_acq_cnt == cfg.rcvd_acq_cnt,, cfg.spinwait_timeout_ns, id)
    csr_spinwait(.ptr(ral.status.acqempty), .exp_data(1'b1));

    if (cfg.m_i2c_agent_cfg.allow_ack_stop) send_ack_stop();
    // add drain time before stop interrupt handler
    cfg.clk_rst_vif.wait_clks(1000);
    cfg.stop_intr_handler = 1;
    `uvm_info(id, "called stop_intr_handler", UVM_MEDIUM)
  endtask // stop_target_interrupt_handler

  // This task is called when tb interrupt handler receives
  // cmdcomplete interrupt.
  virtual task proc_intr_cmdcomplete();
    bit acq_fifo_empty;
    int delay;
    if (cfg.slow_acq) begin
      if($urandom()%2) begin
        acq_fifo_empty = 0;
        while (!acq_fifo_empty) begin
          delay = $urandom_range(1, 50);
          #(delay * 1us);
          read_acq_fifo(1, acq_fifo_empty);
        end
      end
    end else begin
      // read one entry at a time to create acq fifo back pressure
      read_acq_fifo(1, acq_fifo_empty);
    end
    clear_interrupt(CmdComplete, 0);
  endtask // proc_intr_cmdcomplete

  // This task is called when tb interrupt handler receives
  // txstretch interrupt.
  virtual task proc_intr_txstretch();
    bit acq_fifo_empty;
    write_tx_fifo();
    read_acq_fifo(0, acq_fifo_empty);
    // interrupt can't be clear until
    // txfifo get data or acq fifo get entry. So verify_clear can
    // causes deadlock. Set verify_clear to 0 to avoid deadlock
    clear_interrupt(TxStretch, 0);
  endtask // proc_intr_txstretch

  // return target address between, address0, address1 and illegal address
  // illegal address can be return ony if cfg.bad_addr_pct > 0
  // Make sure the last transaction should return good address to guarantee
  // at least one good transaction
  function bit [6:0] get_target_addr();
     if (sent_txn_cnt == (num_trans - 1)) return target_addr0;

     randcase
       cfg.bad_addr_pct: begin
         return illegal_addr;
       end
       (10 - cfg.bad_addr_pct): begin
         randcase
           1: get_target_addr = target_addr0;
           1: get_target_addr = target_addr1;
         endcase
       end
     endcase
  endfunction

  function bit is_target_addr(bit [6:0] addr);
    return (addr == target_addr0 || addr == target_addr1);
  endfunction

endclass : i2c_base_vseq
