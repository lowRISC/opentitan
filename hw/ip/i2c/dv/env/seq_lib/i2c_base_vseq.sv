// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Base vseq class for creating i2c block-level stimulus
// This class contains common helper code and routines for both DUT-Target and DUT-Controller
// stimulus generation and testing. Although it might make more sense to split out code into two
// different class for each operating mode, future multi-controller systems may see both modules
// active simultaneously. This is an intentional use case for certain extension protocols built on
// top of I2C.
//
/////////////////
// Subroutines //
/////////////////
//
// /* Create test configuration, program DUT registers and Agent appropriately. */
// get_timing_values() / print_time_property()
// program_registers()
//
// /* Create write accesses to the FMTFIFO/FDATA for driving DUT-Controller stimulus */
// program_format_flag() / print_format_flag()
//
// /* Create stimulus to drive the i2c_agent to exercise DUT-Target functionality */
// generate_agent_controller_stimulus() / print_agent_controller_txn()
// - create_txn()
// - convert_i2c_txn_to_drv_q()
// - get_transaction_read_data()
// - ack_stop_stim_modifier()
//
// /* Polling-based handlers for the ACQFIFO and TXFIFO (DUT-Target Mode) */
// process_acq() / process_tx()
//
// /* Interrupt-based handlers for operation in DUT-Controller mode */
// process_interrupts()
// /* Interrupt-based handlers for operation in DUT-Target mode */
// process_target_interrupts() / stop_target_interrupt_handler()
// - proc_intr_acqthreshold()
// - proc_intr_txthreshold()
// - proc_intr_unexpstop()
// - proc_intr_hosttimeout()
// - proc_intr_cmdcomplete()
// - proc_intr_txstretch()
// - proc_intr_acqstretch()
//
// /* Interrupt checking helper routines */
// clear_interrupt() / check_one_intr() / count_edge_intr()
//
// /* Helper routines for fifo accesses */
// program_tx_fifo() #TODO Remove, duplicate
// write_tx_fifo() / read_acq_fifo() / empty_acqfifo()

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

  // Start counter including restart.
  // Starting from 1 to match rtl value and easy to trace.
  int start_cnt = 1;

  // This queue stores all the read data bytes the Agent-Controller expects to read back from the
  // DUT. The testbench interrupt handlers will pull data from this queue to be written into the
  // TXFIFO, and hence read back by the agent. Note. that this queue initially includes data bytes
  // that part of transfers not addressed to the DUT, and we post-process the queue
  // (using read_rcvd_q[$]) to remove bytes that in practice the Agent will never receive.
  bit [7:0] read_byte_q[$];
  // Keep a count of the total number of read data bytes we expect the agent to read from the DUT.
  // This is compared to the value the agent reports it has read (cfg.m_i2c_agent_cfg.rcvd_rd_byte)
  // to determine if we should keep adding data from read_byte_q into the TXFIFO.
  int       sent_rd_byte = 0;
  // This queue stores integers corresponding to the length of each generated stimulus read
  // transfer. This is used to remove a certain number of read bytes from the expectation queue
  // (read_byte_q[$]) when a transfer is generated with a bad address.
  int       read_rcvd_q[$];

  // 'stim_id' increments for each new I2C transfer generated as part of our stimulus.
  int       stim_id = 0;

  int       sent_txn_cnt = 0;

  i2c_intr_e intr_q[$];
  bit       expected_intr[i2c_intr_e];

  // The following variables are used only for the ack-stop test (i2c_agent_cfg.allow_ack_stop = 1)
  bit [7:0] pre_feed_rd_data_q[$]; // Always 8'hff
  int       pre_feed_cnt = 0;
  bit       force_ack; // When set, forces the txn we're about to generate to end with an ACK.

  // Setting this bit allows the interrupt handler cleanup code to ensure that any expectations
  // are adjusted if the final read transfer has a bad address.
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
    // thd_sta must at least be long enough to cover the round-trip time
    thd_sta > 3;
    // tsu_sto + t_r must cover the round-trip time.
    tsu_sto > 3 - t_r;
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
      // force derived timing parameters to be positive (correct DUT config)
      // tlow must be at least 2 greater than the sum of t_r + tsu_dat + thd_dat
      // because the flopped clock (see #15003 below) reduces tClockLow by 1.
      tlow    inside {[(t_r + tsu_dat + thd_dat + 2) :
                       (t_r + tsu_dat + thd_dat + 2) + cfg.seq_cfg.i2c_time_range]};
      t_buf   inside {[(tsu_sta - t_r + 1) :
                       (tsu_sta - t_r + 1) + cfg.seq_cfg.i2c_time_range]};
      // These need to be at least 2 cycles to overcome CDC instrumentation's
      // deletion.
      t_sda_unstable     inside {[2 : t_r + thigh - 2]};
      t_sda_interference inside {[2 : t_r + thigh + t_f - 1]};
      t_scl_interference inside {[2 : t_r + thigh - 3]};
    }
  }

  `uvm_object_new

  `define ALL_ACQFIFO_READS_OCCURRED (cfg.rcvd_acq_cnt >= cfg.sent_acq_cnt)
  `define ALL_READS_OCCURRED (cfg.m_i2c_agent_cfg.rcvd_rd_byte >= sent_rd_byte)

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
    sent_rd_byte = 0;
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
      ral.ctrl.ack_ctrl_en.set(cfg.ack_ctrl_en);
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
    ral.host_fifo_config.rx_thresh.set(rx_thresh);
    ral.host_fifo_config.fmt_thresh.set(fmt_thresh);
    csr_update(ral.host_fifo_config);
    ral.target_fifo_config.acq_thresh.set(acq_thresh);
    ral.target_fifo_config.tx_thresh.set(tx_thresh);
    csr_update(ral.target_fifo_config);

    `uvm_info(`gfn, $sformatf("Wrote following register values :\n%s",
      ral.sprint()), UVM_MEDIUM)

    // configure i2c_agent_cfg
    cfg.m_i2c_agent_cfg.timing_cfg = timing_cfg;
    `uvm_info(`gfn, $sformatf("cfg.m_i2c_agent_cfg.timing_cfg\n%p",
        cfg.m_i2c_agent_cfg.timing_cfg), UVM_MEDIUM)

  endtask : program_registers

  virtual task program_format_flag(i2c_item item, string msg = "");
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
    print_format_flag(item, msg);
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
      `uvm_info(`gfn, "clearing fmt_threshold", UVM_DEBUG)
    end
    // TODO: It is NOT possible to clear this interrupt by a simple INTR_STATE write now!
    if (bit'(get_field_val(ral.intr_state.rx_threshold, intr_clear))) begin
      `uvm_info(`gfn, "clearing rx_threshold", UVM_DEBUG)
    end
    if (bit'(get_field_val(ral.intr_state.stretch_timeout, intr_clear))) begin
      `uvm_info(`gfn, "clearing stretch_timeout", UVM_DEBUG)
    end
    if (bit'(get_field_val(ral.intr_state.tx_stretch, intr_clear))) begin
      `uvm_info(`gfn, "clearing tx_stretch", UVM_DEBUG)
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

  // Print all formatting-flags of a particular write to the FDATA fifo.
  //
  // e.g.
  // >   <msg>
  // >   format flags 13'h10bf
  // >   | fbyte | start |  stop | readb | rcont | nakok |
  // >   | 8'hbf |     0 |     0 |     0 |     0 |     1 |
  //
  virtual function void print_format_flag(i2c_item item, string msg = "");
    string str;
    string header_tpl = "  | %5s | %5s | %5s | %5s | %5s | %5s |\n";
    string data_tpl   = "  | 8'h%2x | %5d | %5d | %5d | %5d | %5d |\n";

    str = {$sformatf("\n  \"%s\"\n", msg),
           $sformatf("  format flags 13'h%4x\n",
                     {item.nakok, item.rcont, item.read, item.stop, item.start, item.fbyte})};

    str = {str, $sformatf(header_tpl, "fbyte", "start", "stop", "readb", "rcont", "nakok")};
    str = {str, $sformatf(data_tpl,
                          item.fbyte,
                          item.start,
                          item.stop,
                          item.read,
                          item.rcont,
                          item.nakok)};

    `uvm_info(`gfn, $sformatf("%s", str), UVM_MEDIUM)
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


  // Print out an Agent-Controller transaction generated for stimulus
  //
  function void print_agent_controller_txn(i2c_transaction txn);
    `uvm_info(`gfn, "Generated the following stimulus transaction:", UVM_HIGH)
    for (int i = 0; i < txn.size(); i++) begin
      `uvm_info(`gfn, $sformatf("transfer %0d/%0d:\n%0s",
        i+1, txn.size(), txn[i].sprint()), UVM_HIGH)
    end
  endfunction


  // Randomly choose transfer direction based on cfg.{rd,wr}_pct weights
  virtual function i2c_pkg::rw_e get_read_write();
    randcase
      cfg.wr_pct: return i2c_pkg::WRITE;
      cfg.rd_pct: return i2c_pkg::READ;
    endcase
  endfunction : get_read_write


  // Polling-based ACQFIFO handler
  //
  // This routine waits until the sequence (via cfg.sent_acq_cnt) indicates it has created
  // stimulus that will generate ACQFIFO entires. It then calls read_acq_fifo() until the expected
  // number of ACQFIFO reads have been performed (and checked by the scoreboard).
  //
  virtual task process_acq();

    // Wait until at least some stimulus has been created, that will produce ACQFIFO entires.
    `DV_WAIT(cfg.sent_acq_cnt > 0,, cfg.spinwait_timeout_ns)

    while (!`ALL_ACQFIFO_READS_OCCURRED || (sent_txn_cnt < num_trans)) begin
      bit read_one;

      if (cfg.slow_acq) begin
        int delay = $urandom_range(50, 100);
        #(delay * 1us);
        read_one = 1;
      end

      begin
        bit acq_fifo_empty;
        `uvm_info(`gfn, "process_acq() -> read_acq_fifo() now.", UVM_HIGH)
        read_acq_fifo(read_one, acq_fifo_empty);
      end

      // Clear the 'cmd_complete' interrupt if pending
      begin
        uvm_reg_data_t intr_state;
        csr_rd(.ptr(ral.intr_state), .value(intr_state), .backdoor(1));
        if (get_field_val(ral.intr_state.cmd_complete, intr_state)) begin
          `uvm_info(`gfn, "Clearing pending 'CmdComplete' interrupt.", UVM_HIGH)
          clear_interrupt(CmdComplete, 0);
        end
      end

    end

    `uvm_info(`gfn, "End of process_acq()", UVM_MEDIUM)
  endtask

  // After constructing the randomized stimulus items, this routine writes all data the agent is
  // expecting to receive into the TXFIFO.
  // We need to keep writing data into the fifo until all expected data has been added. Loop until
  // this is true. (Note. that new stimulus may be generated in the meantime, increasing the number
  // of expected bytes dynamically. Keep looping until we catch up to this number.)
  //
  virtual task process_txq();
    // Wait until some amount of stimulus is generated that will read data from the DUT. Since we
    // choose the randomized data as part of stimulus randomization, we can't know what to write
    // until then!
    `DV_WAIT(sent_rd_byte > 0,, cfg.spinwait_timeout_ns, "process_txq")
    `DV_CHECK(cfg.m_i2c_agent_cfg.rcvd_rd_byte == 0)

    while (// The agent is expecting to read more data. Keep adding them to the TXFIFO.
           cfg.m_i2c_agent_cfg.rcvd_rd_byte < sent_rd_byte ||
           // There are more transactions to drive. Don't exit the loop early in this case.
           sent_txn_cnt < num_trans) begin
      cfg.clk_rst_vif.wait_clks(1);
      write_tx_fifo(.add_delay(cfg.slow_txq));
    end
  endtask

  // Generate a new Agent-Controller stimulus transaction
  //
  // This routine wraps a number of things that need to happen alongside the actual randomization
  // - Randomize a new transaction (START + transfers + STOP) + stim_id
  // - Modify the transaction to stimulate degenerate behaviours
  //   - ACK/NACK-ing to stimulate 'unexp_stop' interrupt (ack-stop test)
  // - Provide a queue of stimulus seq_items to the agent sequence (drv_type/wdata/rdata) that
  //   control the driver.
  // - Control testbench CSR-side routines to drive DUT inputs to match the expected transaction
  //   - Extract the required data bytes for testbench handler routines to populate TXFIFO with
  //     the expected read data
  //     - Ensure bytes associated with transfers with bad-addresses (i.e. not matching the DUT's
  //       configured addresses) are dropped/not added to the TXFIFO.
  //
  virtual function void generate_agent_controller_stimulus(
    // This function outputs a queue of objects that can be passed to one of the agent sequences
    // that will drive the generated I2C transaction.
    // This is specifically intended to be passed to the i2c_base_seq class variable req_q[$],
    // which derived sequences use to define the stimulus they will generate. Users of this routine
    // should assign this returned queue of objects to 'req_q' when constructing an agent sequence.
    ref i2c_item drv_q[$]
  );

    // Create the randomized transaction
    // - A 'transaction' in i2c parlance has a specific meaning, which is a single continuous
    //   operation by a single controller, starting and stopping with START and STOP conditions,
    //   and possibly subdivided by RSTARTs into one or more smaller 'transfers'.
    // - The return type of this routine is a queue of i2c_item's, each of which represent a
    //   a transfer that makes up the larger transaction.
    i2c_transaction txn = create_txn();

    // Modify the transaction generation process to instigate degenerate behaviour
    // - "ack-stop" test changes the way we drive/determine the ACKing behaviour for some bytes.
    if (cfg.m_i2c_agent_cfg.allow_ack_stop) ack_stop_stim_modifier(txn);

    // Generate control items in the form expected by the i2c_agent to drive the stimulus
    convert_i2c_txn_to_drv_q(txn, drv_q);

    // Calculate the number of read-data bytes we expect to see based on this stimulus
    // - read_rcvd_q[$] - queue of num. bytes in each read transfer
    // - sent_rd_byte - total read bytes
    // - read_byte_q[$] - a queue of all data bytes that will be written into the TXFIFO
    get_transaction_read_data(txn);

    // (LOGGING-ONLY) Print out the transaction
    print_agent_controller_txn(txn);
  endfunction

  // Create a new valid I2C transaction for DUT-Target stimulus.
  //
  // This randomized transaction is constrained by a number of 'env_cfg' variables
  // - cfg.min_data/cfg.max_data
  // - cfg.rs_pct
  // - cfg.min_xfer_len
  //
  virtual function i2c_transaction create_txn();
    int seed = $urandom;

    int min_num_transfers, max_num_transfers;

    // A temporary, used to randomize the total number of data bytes in the transaction.
    int unsigned num_data_total;
    // A temporary, used to randomize the total number of transfers in the transaction.
    int num_transfers;
    // A temporary used to succintly randomize the structure of the transaction.
    // Each element in the array will represent the number of data bytes in each transfer that
    // makes up the larger created transaction.
    int unsigned transfer_lengths[];

    // A local variable used to accumulate the new transaction as we construct it.
    i2c_transaction txn;

    // Randomize the number of data bytes total in the transaction.
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(num_data_total,
      num_data_total inside {[cfg.min_data : cfg.max_data]};
    )

    min_num_transfers = (cfg.min_num_transfers >= 1) ? cfg.min_num_transfers : 1;
    max_num_transfers = (cfg.max_num_transfers == 0)             ? num_data_total :
                        (cfg.max_num_transfers > num_data_total) ? num_data_total :
                        cfg.max_num_transfers;
    `DV_CHECK(min_num_transfers <= max_num_transfers)

    // Randomize the number of transfers in the transaction.
    // TODO(#23920) Consider re-implementing to avoid waiver.
    num_transfers = $dist_normal( // verilog_lint: waive invalid-system-task-function
      /* seed */ seed,
      /* mean */ int'(num_data_total * real'(cfg.rs_pct / 100.0)),
      /* stddev */ int'(num_data_total * 0.10)
    );
    // Saturate into the possible range if we happen to fall outside of it.
    if (num_transfers < min_num_transfers ||
        num_transfers > max_num_transfers) begin
      `uvm_info(`gfn, $sformatf("num_transfers (%0d) outside valid range (%0d - %0d), saturating.",
        num_transfers, 1, num_data_total), UVM_DEBUG)
      if (num_transfers < min_num_transfers) num_transfers = min_num_transfers;
      if (num_transfers > max_num_transfers) num_transfers = max_num_transfers;
    end

    // Next randomize the number of data bytes in each transfer.
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(transfer_lengths,
      transfer_lengths.size() == num_transfers;
      transfer_lengths.sum() == num_data_total;
      foreach (transfer_lengths[i]) {
        // Bound the size of each transfer to limit the solve space to positive integers
        transfer_lengths[i] inside {[cfg.min_xfer_len : num_data_total]};
      }
      // Don't place RSTARTs too close to the start or end of the transaction.
      transfer_lengths[0] > 0;
      transfer_lengths[num_transfers - 1] > 0;
    )

    // Loop over the list of transfers we wish to construct, adding in data and control signals
    // as appropriate. The address and data-direction of each is chosen randomly at this point.
    foreach (transfer_lengths[i]) begin
      uint len = transfer_lengths[i];
      i2c_item xfer;
      `uvm_create_obj(i2c_item, xfer)

      xfer.stim_id = this.stim_id++;
      xfer.addr = get_target_addr(); // (randomly) Get a new address for the next transfer
      xfer.addr_ack = is_target_addr(xfer.addr[6:0]) ? i2c_pkg::ACK : i2c_pkg::NACK;
      xfer.dir = get_read_write(); // (randomly) Choose the direction of the transfer
      xfer.bus_op = (xfer.dir == i2c_pkg::READ) ? BusOpRead : BusOpWrite;
      xfer.num_data = len;

      for (int j = 0; j < len; j++) begin
        // By default, everything should be ACK'd except for the final byte of any read transfer
        acknack_e acknack = ((xfer.bus_op == BusOpRead) && (j == len - 1)) ? i2c_pkg::NACK :
                                                                             i2c_pkg::ACK;
        xfer.data_ack_q.push_back(acknack);
        xfer.data_q.push_back($urandom);
      end

      // Add the control flags to show how each transaction should start and end
      if (num_transfers == 1) begin
        // Special case for a transaction with one transfer -> No RSTARTs
        xfer.start = 1;
        xfer.stop = 1;
      end else begin
        case (i)
          0: begin // First transfer
            xfer.start = 1;
            xfer.rstart_back = 1;
          end
          num_transfers - 1: begin // Last transfer
            xfer.rstart_front = 1;
            xfer.stop = 1;
          end
          default: begin // Any transfer not at the start/end of the txn must begin and end with
            // rstart conditions.
            xfer.rstart_front = 1;
            xfer.rstart_back = 1;
          end
        endcase
      end

      // Add the transfer into the transaction.
      txn.push_back(xfer);
    end

    // Print a summary of the randomized transaction
    //
    // e.g.
    //
    // > Randomized the following transaction:
    // > total_bytes=19
    // > num_xfers=4
    // > xfers=
    // >   5-byte WRITE
    // >   3-byte READ
    // >   7-byte WRITE
    // >   4-byte WRITE
    //
    begin
      string xfers_str = "";
      foreach (txn[i]) begin
        xfers_str = {xfers_str, $sformatf("  %0d-byte %0s\n", txn[i].num_data, txn[i].dir.name())};
      end
      `uvm_info(`gfn, $sformatf(
        {"Randomized the following transaction:\n",
        "total_bytes=%0d\n",
        "num_xfers=%0d\n",
        "xfers=\n%s"},
        num_data_total, num_transfers, xfers_str), UVM_HIGH)
    end

    return txn;
  endfunction : create_txn


  // The i2c_driver is controlled by providing it a queue of sequence items, each of which
  // specify the driving behaviour with the following fields:
  // - drv_type
  // - wdata
  // - rdata
  // This function converts an i2c_item targeted at the transfer-level to a queue of items that
  // control the driver to create an equivalent bus state.
  //
  // This behaviour isn't ideal, as we are re-using the i2c_item to do something completely
  // different to how it is used elsewhere. In fact, the i2c_item type would be better renamed
  // to a i2c_transfer_item, as really this is the level of abstraction it operates at.
  // The 3 fields above are not used, except for controlling the i2c_driver.
  // #TODO Move to agent sequence ideally. (also see #14825)
  //
  virtual function void convert_i2c_txn_to_drv_q(i2c_transaction txn, ref i2c_item drv_q[$]);

    // Loop over each transfer, determine what to drive based on the control flags
    foreach (txn[transfer_i]) begin
      i2c_item xfer = txn[transfer_i];

      // The transfer must begin with a 'START' or 'RSTART' condition
      if (xfer.start) begin
        // 'START' condition begins the transfer (and transaction)
        i2c_item start_txn;
        `uvm_create_obj(i2c_item, start_txn)
        start_txn.drv_type = HostStart;
        drv_q.push_back(start_txn);
      end else if (xfer.rstart_front) begin
        // 'RSTART' condition begins the transfer (which is only possible if the previous
        // transfer ends with an RSTART).
        // Sending duplicate messages with .drv_type = HostRStart would cause the driver to
        // produce invalid traffic, so simply omit sending it here.
        `uvm_info(`gfn, "Omitting .drv_type = HostRStart item from driver queue.", UVM_FULL)
      end else begin
        `uvm_fatal(`gfn, "Can't create a transfer that doesn't start with either START or RSTART!")
      end

      // Add the address+direction byte
      begin
        i2c_item addr_txn;
        `uvm_create_obj(i2c_item, addr_txn)
        addr_txn.drv_type = HostData;
        addr_txn.wdata[7:1] = xfer.addr[6:0];
        addr_txn.wdata[0] = xfer.dir;
        drv_q.push_back(addr_txn);
      end

      // Add items for all the data bytes
      foreach (xfer.data_q[i]) begin
        case (xfer.bus_op)
          BusOpWrite: begin
            // For write bytes, we drive the data using 'HostData'
            i2c_item data_txn;
            `uvm_create_obj(i2c_item, data_txn)
            data_txn.drv_type = HostData;
            data_txn.wdata = xfer.data_q[i];
            drv_q.push_back(data_txn);
          end
          BusOpRead: begin
            // For read bytes, we wait 8 bit-periods then ack or nack. (The driver's behaviour
            // for 'HostAck' and 'HostNAck' drive types both include this 8-bit wait).
            i2c_item acknack_txn;
            `uvm_create_obj(i2c_item, acknack_txn)
            acknack_txn.drv_type = (xfer.data_ack_q[i] == i2c_pkg::ACK) ? HostAck : HostNAck;
            drv_q.push_back(acknack_txn);
          end
          default:;
        endcase
      end

      // Add the 'STOP' or 'RSTART' condition to end the transfer
      if (xfer.stop) begin
        // 'STOP' condition ends the transfer (and transaction)
        i2c_item stop_txn;
        `uvm_create_obj(i2c_item, stop_txn)
        stop_txn.drv_type = HostStop;
        drv_q.push_back(stop_txn);
      end else if (xfer.rstart_back) begin
        // 'RSTART' condition ends the transfer
        i2c_item rstart_txn;
        `uvm_create_obj(i2c_item, rstart_txn)
        rstart_txn.drv_type = HostRStart;
        drv_q.push_back(rstart_txn);
      end else begin
        `uvm_fatal(`gfn, "Can't create a transfer that doesn't end with either STOP or RSTART!")
      end
    end

  endfunction : convert_i2c_txn_to_drv_q


  // Post-process the randomized transaction stimulus to extract information about read transfers
  // For stimulus generation, we need to ensure the correct data is fed into the TXFIFO such
  // that it matches the expectation.
  //
  // #TODO Don't form expectations this way, use the bus monitor to reconstruct the exp. instead.
  //
  function void get_transaction_read_data(i2c_transaction txn);
    foreach (txn[transfer_i]) begin
      i2c_item xfer = txn[transfer_i];
      if (xfer.bus_op == BusOpRead) begin
        // Store into a queue the length of each read transfer.
        read_rcvd_q.push_back(xfer.num_data);
        // Accumulate the total number of read data bytes.
        sent_rd_byte += xfer.num_data;
        // Copy the read data bytes for interrupt handlers to pickup and write into the TXFIFO.
        foreach (xfer.data_q[i]) read_byte_q.push_back(xfer.data_q[i]);
      end
    end
  endfunction : get_transaction_read_data

  // This function modifies a pre-generated i2c transaction to produce stimulus for the
  // ack-stop test. This test aims to trigger the 'unexp_stop' interrupt.
  //
  function void ack_stop_stim_modifier(i2c_transaction txn);

    foreach (txn[transfer_i]) begin
      i2c_item xfer = txn[transfer_i];

      if (xfer.bus_op == BusOpRead) begin
        acknack_e random_acknack;

        // Ack-Stop test mode can introduce a non-normal ACK bit at the end of each read transfer.
        // When enabled, randomly ACK or NACK the final byte of each individual read transfer.
        `DV_CHECK_STD_RANDOMIZE_FATAL(random_acknack)
        xfer.data_ack_q[$] = random_acknack;

        // In Ack-Stop test mode, we may need to overwrite the data byte from the pre-randomized
        // value. Values are pushed into the 'pre_feed_rd_data_q[$]' as needed, and overwrite read
        // data bytes in the generated transactions from first to last.
        foreach (xfer.data_q[i]) begin
          if (pre_feed_rd_data_q.size() > 0) xfer.data_q[i] = pre_feed_rd_data_q.pop_front();
        end
      end
    end

    // If the final transfer in the transaction is a READ , then 'force_ack' can also be used
    // to always ACK the final byte.
    if (force_ack) begin
      `DV_CHECK(txn[$].bus_op == BusOpRead, "Can't force_ack if the final transfer wasn't a READ!")
      // Force the final byte to be ACK'd
      txn[$].data_ack_q[$] = i2c_pkg::ACK;
    end

  endfunction : ack_stop_stim_modifier

  virtual task proc_intr_acqthreshold; endtask
  virtual task proc_intr_txthreshold; endtask
  virtual task proc_intr_unexpstop; endtask
  virtual task proc_intr_hosttimeout; endtask

  // Target-mode interrupt handling.
  //
  // This routine loops through all active target-mode wired interrupts, and
  // randomly calls one of the handler routines.
  virtual task process_target_interrupts();
    bit acq_fifo_empty;
    bit read_one = 0;
    logic [NUM_MAX_INTERRUPTS-1:0] target_interrupts_mask = '0;

    target_interrupts_mask |= (1 << AcqThreshold) |
                              (1 << CmdComplete)  |
                              (1 << TxStretch)    |
                              (1 << TxThreshold)  |
                              (1 << AcqStretch)   |
                              (1 << UnexpStop)    |
                              (1 << HostTimeout);

    // Add a small amount of latency, just to prevent loops when no interrupts
    // are pending.
    @(posedge cfg.clk_rst_vif.clk);

    if (cfg.intr_vif.pins & target_interrupts_mask) begin
      randcase
        cfg.intr_vif.pins[AcqThreshold]: proc_intr_acqthreshold(); // status
        cfg.intr_vif.pins[CmdComplete]:  proc_intr_cmdcomplete();  // event
        cfg.intr_vif.pins[TxStretch]:    proc_intr_txstretch();    // status
        cfg.intr_vif.pins[TxThreshold]:  proc_intr_txthreshold();  // status
        cfg.intr_vif.pins[AcqStretch]:   proc_intr_acqstretch();   // status
        cfg.intr_vif.pins[UnexpStop]:    proc_intr_unexpstop();    // event
        cfg.intr_vif.pins[HostTimeout]:  proc_intr_hosttimeout();  // event
      endcase
    end

    // This cfg option can be used to empty the acqfifo, typically at the end of a test.
    if (cfg.read_all_acq_entries) begin
      `uvm_info(`gfn, "cfg.read_all_acq_entries -> read_acq_fifo() now.", UVM_HIGH)
      read_acq_fifo(.read_one(0), .acq_fifo_empty(acq_fifo_empty));
    end

    // The variable "expected_intr[]" is used to keep track of interrupts the testbench
    // expects the possibility of seeing asserted. If an interrupt is asserted that is
    // not marked in this way, throw an error.
    for (int i = 0; i < NumI2cIntr; i++) begin
      i2c_intr_e my_intr = i2c_intr_e'(i);
      if ((!expected_intr.exists(my_intr)) && // Not expected
          (cfg.intr_vif.pins[i] !== 0)) begin // Triggered
        `uvm_error("process_target_interrupts",
                   $sformatf("Unexpected interrupt is set %s", my_intr.name))
      end
    end

    // When transfers with bad addresses are dropped, the queue (read_byte_q) of read data bytes
    // the Agent-Controller expects to read back from the DUT also needs adjusting.
    // This is normally done in write_tx_fifo(), but for the last bad read command, we have to do
    // the adjustment here because we will not call 'write_tx_fifo'.
    if ((cfg.bad_addr_pct > 0) &&
        adjust_exp_read_byte && // Set in stop_target_interrupt_handler()
        `ALL_ACQFIFO_READS_OCCURRED) begin
      while (cfg.m_i2c_agent_cfg.read_addr_q.size > 0) begin
        bit is_valid = cfg.m_i2c_agent_cfg.read_addr_q.pop_front();
        if (!is_valid) begin
          int read_size = read_rcvd_q.pop_front();
         `uvm_info(`gfn, $sformatf("Adjusting 'sent_rd_byte' counter down by %0d from %0d -> %0d",
                                   read_size, sent_rd_byte, sent_rd_byte - read_size), UVM_FULL)
          repeat (read_size) void'(read_byte_q.pop_front());
          sent_rd_byte -= read_size;
        end
      end
    end
  endtask

  // Fill the TXFIFO for a single read transaction.
  //
  task write_tx_fifo(bit add_delay = 0);
    uvm_reg_data_t data;
    int read_size;
    int rd_txfifo_timeout_ns = 10_000_000;
    // indefinite time
    int tx_empty_timeout_ns = 500_000_000;

    string id = "write_tx_fifo";

    // If there is a chance of generating stimulus transactions with bad addresses, check if the
    // next transfer at the head of the queue has a bad address. If so, drop it from all
    // expectations, as the DUT should ignore it.
    if (cfg.bad_addr_pct > 0) begin
      bit is_valid;
      is_valid = cfg.m_i2c_agent_cfg.read_addr_q.pop_front();
      if (!is_valid) begin
        read_size = read_rcvd_q.pop_front();
        `uvm_info(`gfn, $sformatf("Adjusting 'sent_rd_byte' counter down by %0d from %0d -> %0d",
                                  read_size, sent_rd_byte, sent_rd_byte - read_size), UVM_FULL)
        repeat (read_size) void'(read_byte_q.pop_front());
        sent_rd_byte -= read_size;
        return;
      end
    end

    if (read_rcvd_q.size() > 0) begin
      read_size = read_rcvd_q.pop_front();
      `uvm_info(id, $sformatf("read_size :%0d", read_size), UVM_HIGH)
    end else begin
      // In ack-stop test mode, we need to feed 1 extra data byte into the TXFIFO at the end
      // of the transaction to avoid dead-lock.
      if (cfg.m_i2c_agent_cfg.allow_ack_stop) begin
        `uvm_info(id, "Feeding extra data byte (0xff) for ack/stop now.", UVM_HIGH)
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
      if (read_byte_q.size() > 0) begin
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
            csr_rd(.ptr(ral.status.txfull), .value(data));
            // if tx fifo is full, real acq fifo to remove
            // tx_stretch condition
            if (data) begin
              bit acq_fifo_empty;
              `uvm_info(`gfn, "write_tx_fifo() -> read_acq_fifo() now.", UVM_HIGH)
              read_acq_fifo(.read_one(0), .acq_fifo_empty(acq_fifo_empty));
            end
          end

        end else begin
          csr_spinwait(.ptr(ral.status.txfull), .exp_data(1'b0),
                       .timeout_ns(rd_txfifo_timeout_ns));
        end

        begin
          bit [7:0] wdata = read_byte_q.pop_front();
          // (ack-stop test) Only write to the txfifo now if there is no pre-feed data
          if (pre_feed_cnt == 0) begin
            csr_wr(.ptr(ral.txdata), .value(wdata));
            `uvm_info(id, $sformatf("Wrote 0x%0x to txdata", wdata), UVM_HIGH)
          end else begin
            pre_feed_cnt--;
          end
        end

        read_size--;
      end
    end
  endtask

  // when read_one = 1. check acqempty and read a single entry
  // When read_one = 0, empty the acqfifo (read acq fifo up to acqlvl)
  task read_acq_fifo(bit read_one, ref bit acq_fifo_empty);
    uvm_reg_data_t read_data;
    i2c_acqdata_item obs;
    acq_fifo_empty = 0;
    if (read_one) begin
    // Polling if status.acqempty is zero and skip read fifo
    // if fifo is empty.
      csr_rd(.ptr(ral.status.acqempty), .value(acq_fifo_empty));
      read_data = (acq_fifo_empty)? 0 : 1;
    end else csr_rd(.ptr(ral.target_fifo_status.acqlvl), .value(read_data));

    repeat(read_data) begin
      csr_rd(.ptr(ral.acqdata), .value(read_data));
      obs = acq2item(read_data);
      `uvm_info(`gfn, $sformatf("read_acq_fifo() read data 3'h%3x (.signal=%s, .abyte=2'h%2x)",
        read_data, obs.signal.name(), obs.abyte), UVM_HIGH)
    end

    if (read_data == 0) begin
      cfg.clk_rst_vif.wait_clks(1);
      `uvm_info(`gfn, "read_acq_fifo() fifo is now empty", UVM_DEBUG)
    end

    `uvm_info(`gfn, $sformatf(
      "After read_acq_fifo() : cfg.sent_acq_cnt=%0d cfg.rcvd_acq_cnt=%0d",
      cfg.sent_acq_cnt, cfg.rcvd_acq_cnt), UVM_HIGH)
    `uvm_info(`gfn, $sformatf(
      "After read_acq_fifo() : sent_rd_byte=%0d cfg.m_i2c_agent_cfg.rcvd_rd_byte=%0d",
      cfg.sent_acq_cnt, cfg.rcvd_acq_cnt), UVM_HIGH)
  endtask : read_acq_fifo

  virtual task empty_acqfifo();
    bit acq_fifo_empty;
    read_acq_fifo(.read_one(0), .acq_fifo_empty(acq_fifo_empty));
  endtask : empty_acqfifo


  // Extra stimulus hook for use in the i2c_target_ack_stop_vseq
  virtual task send_ack_stop; endtask


  // This task waits for all transaction stimulus to complete, then stops any further execution of
  // the testbench's interrupt handling routines. This is part of the end-of-test cleanup.
  //
  virtual task stop_target_interrupt_handler();
    string id = "stop_target_interrupt_handler()";

    // Wait until all test stimulus has been driven
    `DV_CHECK(num_trans != 0)
    `DV_WAIT((sent_txn_cnt > 0) && (sent_txn_cnt == num_trans),,
             cfg.long_spinwait_timeout_ns, id)

    // Read out all acqfifo entries to cleanup at the end of the test
    cfg.read_all_acq_entries = 1;

    // If the final transfer is a read with a bad address, we need to go down a slightly different
    // codepath (see 'adjust_exp_read_byte') to ensure our expectations are formed correctly.
    if ((cfg.bad_addr_pct > 0) && cfg.rd_pct != 0) begin
      `DV_WAIT(sent_rd_byte > 0,, cfg.spinwait_timeout_ns, id)
      adjust_exp_read_byte = 1;
    end

    `DV_WAIT(`ALL_READS_OCCURRED,,, "Failed check for ALL_READS_OCCURRED")
    `DV_WAIT(`ALL_ACQFIFO_READS_OCCURRED,,, "Failed check for ALL_ACQFIFO_READS_OCCURRED")

    // Wait until all acqfifo entries have been read by the testbench, as we can't check our
    // predictions until these observations are captured.
    csr_spinwait(.ptr(ral.status.acqempty), .exp_data(1'b1));

    // For the ack-then-stop test mode, we stimulate an extra final transaction which ends with
    // the test stimulus we expect to trigger the associated interupt (This routine sets
    // force_ack = 1 and cfg.wr_pct = 0 to guarantee this).
    if (cfg.m_i2c_agent_cfg.allow_ack_stop) send_ack_stop();

    // Add some drain time before stopping all target-mode interrupt handlers
    cfg.clk_rst_vif.wait_clks(1000);

    `uvm_info(`gfn, "Target-Mode interrupt handlers stopped now.", UVM_MEDIUM)
    cfg.stop_intr_handler = 1; // Stop the process_target_interrupts() irq-handler routine.
  endtask : stop_target_interrupt_handler


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
          `uvm_info(`gfn, "proc_intr_cmdcomplete() -> (SLOW) read_acq_fifo() now.", UVM_HIGH)
          read_acq_fifo(.read_one(1), .acq_fifo_empty(acq_fifo_empty));
        end
      end
    end else begin
      // read one entry at a time to create acq fifo back pressure
      `uvm_info(`gfn, "proc_intr_cmdcomplete() -> read_acq_fifo() now.", UVM_HIGH)
      read_acq_fifo(.read_one(1), .acq_fifo_empty(acq_fifo_empty));
    end
    clear_interrupt(CmdComplete, 0);
  endtask // proc_intr_cmdcomplete

  // This task is called when tb interrupt handler receives
  // txstretch interrupt.
  virtual task proc_intr_txstretch();
    bit acq_fifo_empty;
    write_tx_fifo();
    `uvm_info(`gfn, "proc_intr_txstretch() -> read_acq_fifo() now.", UVM_HIGH)
    read_acq_fifo(.read_one(0), .acq_fifo_empty(acq_fifo_empty));
    // interrupt can't be clear until
    // txfifo get data or acq fifo get entry. So verify_clear can
    // causes deadlock. Set verify_clear to 0 to avoid deadlock
    clear_interrupt(TxStretch, 0);
  endtask // proc_intr_txstretch

  // The TB's interrupt handler should call this routine whenever the "acq_stretch"
  // interrupt is pending.
  //
  virtual task proc_intr_acqstretch();
    // 'AcqStretch' can mean two things
    // 1) The N-Byte ACK counter is zero. (if this feature is enabled)
    // 2) The ACQFIFO is full

    bit [TL_DW-1:0] status;
    bit             ack_ctrl_stretch;
    bit             acq_full;

    csr_rd(.ptr(ral.status), .value(status));
    ack_ctrl_stretch = bit'(get_field_val(ral.status.ack_ctrl_stretch, status));
    acq_full = bit'(get_field_val(ral.status.acqfull, status));

    // 1) (if enabled) Add a random number to the N-Byte ACK counter, allowing the FSM to continue.
    if (ack_ctrl_stretch) begin
      int auto_ack_bytes = $urandom_range(1, 30);
      csr_wr(.ptr(ral.target_ack_ctrl.nbytes), .value(auto_ack_bytes));
    end

    // 2) Read the ACQFIFO if it is currently full.
    if (acq_full) begin
      bit acq_fifo_empty = 0;
      `uvm_info(`gfn, "proc_intr_acqstretch() -> read_acq_fifo() as currently full.", UVM_HIGH)
      case (cfg.slow_acq)
        // Read the fifo until empty.
        1'b0: read_acq_fifo(.read_one(0), .acq_fifo_empty(acq_fifo_empty));
        // Read the fifo until empty, but slowly (1-word at a time with delays inbetweeen).
        1'b1: begin
          while (!acq_fifo_empty) begin
            int delay = $urandom_range(50, 100);
            #(delay * 1us);
            read_acq_fifo(.read_one(1), .acq_fifo_empty(acq_fifo_empty));
          end
        end
        default:;
      endcase
    end

  endtask: proc_intr_acqstretch

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
       (100 - cfg.bad_addr_pct): begin
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

  // Check an interrupt matches our expectation
  // - Check that csr.intr_state[idx] == exp_val
  // - Check the wired irq intr_vif.pins[idx] == exp_val
  //
  virtual task check_one_intr(i2c_intr_e intr, bit exp_val);
    bit [TL_DW-1:0] obs_intr_state;
    bit exp_pin;

    csr_rd(.ptr(ral.intr_state), .value(obs_intr_state));
    `DV_CHECK_EQ(obs_intr_state[intr], exp_val)
    `DV_CHECK_EQ(cfg.intr_vif.pins[intr], exp_val)
  endtask : check_one_intr

  virtual task count_edge_intr(i2c_intr_e intr, ref uint poscnt, ref uint negcnt);
    forever begin
      @(cfg.intr_vif.pins[intr]);
      case (cfg.intr_vif.pins[intr])
        1'b0: negcnt++;
        1'b1: poscnt++;
        default:;
      endcase
    end
  endtask: count_edge_intr

endclass : i2c_base_vseq
