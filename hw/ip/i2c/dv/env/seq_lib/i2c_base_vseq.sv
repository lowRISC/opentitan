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
  rand bit                    rw_bit; // 0 write, 1 read
  rand bit   [7:0]            wr_data[$];
  rand bit   [9:0]            addr;  // support both 7-bit and 10-bit target address
  rand bit   [6:0]            target_addr0;  // Target Address 0
  rand bit   [6:0]            target_addr1;  // Target Address 1
  rand bit   [7:0]            txdata;
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

  // host timeout ctrl value
  bit [31:0]                  host_timeout_ctrl = 32'hffff;
  // Start counter including restart. Starting from 1 to match rtl value
  // and easy to trace.
  int start_cnt = 1;
  int read_rcvd[$];
  int full_txn_num = 0;
  int exp_rd_id = 0;
  int exp_wr_id = 0;
  i2c_item read_txn_q[$];
  int tran_id = 0;
  int sent_txn_cnt = 0;

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
      // tlow must be at least 2 greater than the sum of t_r + tsu_dat + thd_dat
      // because the flopped clock (see #15003 below) reduces tClockLow by 1.
      thigh == (thd_sta + tsu_sta + t_r);
      tlow    inside {[(t_r + tsu_dat + thd_dat + 2) :
                       (t_r + tsu_dat + thd_dat + 2) + cfg.seq_cfg.i2c_time_range]};
      t_buf   inside {[(tsu_sta - t_r + 1) :
                       (tsu_sta - t_r + 1) + cfg.seq_cfg.i2c_time_range]};
      t_sda_unstable     inside {[0 : t_r + thigh + t_f - 1]};
      t_sda_interference inside {[0 : t_r + thigh + t_f - 1]};
      t_scl_interference inside {[0 : t_r + thigh + t_f - 1]};
    }
  }

  constraint rw_bit_c {
    (cfg.trans_type == ReadOnly) -> rw_bit == 1;
    (cfg.trans_type == WriteOnly) -> rw_bit == 0;
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

  // TODO remove input arguments
  virtual task initialization(if_mode_e mode = Host);
    wait(cfg.m_i2c_agent_cfg.vif.rst_ni);
    if (mode == Host) begin
      i2c_init(Host);
      agent_init(Device);
    end else begin
      i2c_init(Device);
      agent_init(Host);
    end
    `uvm_info(`gfn, $sformatf("\n  initialization is done, DUT/AGENT = %s",
        (mode == Host) ? "Host/Target" : "Target/Host"), UVM_LOW)
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
    // TODO: initialization for the agent running in Host mode
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
      // TODO: more initialization for the host running Target mode
      ral.target_id.address0.set(target_addr0);
      ral.target_id.mask0.set(7'h7f);
      ral.target_id.address1.set(target_addr1);
      ral.target_id.mask1.set(7'h7f);
      csr_update(ral.target_id);
      // Host timeout control
      ral.host_timeout_ctrl.set(this.host_timeout_ctrl);
      csr_update(ral.host_timeout_ctrl);
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
        cfg.m_i2c_agent_cfg.timing_cfg), UVM_MEDIUM)

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
    if (bit'(get_field_val(ral.intr_state.stretch_timeout, intr_clear))) begin
      `uvm_info(`gfn, "\n  clearing stretch_timeout", UVM_DEBUG)
    end
    if (bit'(get_field_val(ral.intr_state.tx_empty, intr_clear))) begin
      `uvm_info(`gfn, "\n  clearing tx_empty", UVM_DEBUG)
    end
    if (bit'(get_field_val(ral.intr_state.tx_nonempty, intr_clear))) begin
      `uvm_info(`gfn, "\n  clearing tx_nonempty", UVM_DEBUG)
    end
    if (bit'(get_field_val(ral.intr_state.tx_overflow, intr_clear))) begin
      `uvm_info(`gfn, "\n  clearing tx_overflow", UVM_DEBUG)
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
      str = {str, $sformatf("\n    en_fmt_overflow       %b", cfg.seq_cfg.en_fmt_overflow)};
      str = {str, $sformatf("\n    en_rx_overflow        %b", cfg.seq_cfg.en_rx_overflow)};
      str = {str, $sformatf("\n    en_rx_watermark       %b", cfg.seq_cfg.en_rx_watermark)};
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
    csr_rd(.ptr(ral.fifo_status.acqlvl), .value(acqlvl));
    `DV_CHECK_EQ(acqlvl, (num_bytes+2)) // addr byte + data bytes + junk byte
    for (int i = 0; i < (num_bytes+2); i++) begin
      csr_rd(.ptr(ral.acqdata), .value({signal,abyte}));
    end
  endtask : read_acqdata

  task program_stretch_ctrl(bit stop_acq, bit stop_tx, bit en_addr_acq, bit en_addr_tx);
     csr_wr(.ptr(ral.stretch_ctrl.stop_acq), .value(stop_acq));
     csr_wr(.ptr(ral.stretch_ctrl.stop_tx), .value(stop_tx));
     csr_wr(.ptr(ral.stretch_ctrl.en_addr_acq), .value(en_addr_acq));
     csr_wr(.ptr(ral.stretch_ctrl.en_addr_tx), .value(en_addr_tx));
  endtask : program_stretch_ctrl

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
  function void print_wr_data(i2c_item myq[$]);
    int idx = 1;
    `uvm_info("seq", $sformatf("q size:%0d", myq.size()), UVM_MEDIUM)
    foreach (myq[i]) begin
      if (myq[i].rstart) begin
        `uvm_info("seq", $sformatf("idx %0d RS rw:%0d", start_cnt++, myq[i].read), UVM_MEDIUM)
        idx = 1;
      end else begin
        `uvm_info("seq", $sformatf("%2d: 0x%2x", idx++, myq[i].wdata), UVM_MEDIUM)
      end
    end
  endfunction

  // Set rw bit based on cfg rd/wr pct
  function bit get_read_write();
    bit rw;
    randcase
      cfg.wr_pct: rw = 0;
      cfg.rd_pct: rw = 1;
    endcase
    return rw;
  endfunction // get_read_write

  // Read acqdata and pass to scoreboard until
  // send and rcv cnt become the same.
  virtual task process_acq();
    uvm_reg_data_t read_data;
    i2c_item obs;
    bit is_read;

    `DV_WAIT(cfg.sent_acq_cnt > 0,, cfg.spinwait_timeout_ns, "process_acq")

    while (cfg.sent_acq_cnt != cfg.rcvd_acq_cnt) begin
      // polling status.acqempty == 0
      csr_rd(.ptr(ral.status.acqempty), .value(read_data));
      if (read_data == 0) begin
        // read one entry and compare
        csr_rd(.ptr(ral.acqdata), .value(read_data));
        `uvm_info("process_acq", $sformatf("acq data %x", read_data), UVM_MEDIUM)
        `uvm_create_obj(i2c_item, obs);
        obs = acq2item(read_data);
        is_read = obs.read;

        obs.tran_id = cfg.rcvd_acq_cnt++;
        p_sequencer.target_mode_wr_obs_port.write(obs);
      end else begin // if (read_data == 0)
        cfg.clk_rst_vif.wait_clks(1);
        `uvm_info("process_acq", $sformatf("acq_dbg: sent:%0d rcvd:%0d acq_is_empty",
                                           cfg.sent_acq_cnt, cfg.rcvd_acq_cnt), UVM_HIGH)
      end
    end
  endtask

  // Polling read_rcvd q and fetch read data to txdata fifo
  virtual task process_txq();
    uvm_reg_data_t data;
    int read_size;
    int rd_txfifo_timeout_ns = 50_000;

    `DV_WAIT(cfg.m_i2c_agent_cfg.sent_rd_byte > 0,, cfg.spinwait_timeout_ns, "process_txq")
    forever begin
      @(cfg.m_i2c_agent_cfg.vif.cb);
      if (read_rcvd.size() > 0) begin
        read_size = read_rcvd.pop_front();
      end

      while (read_size > 0) begin
        @(cfg.m_i2c_agent_cfg.vif.cb);
        if (read_txn_q.size() > 0) begin
          i2c_item item;
          //check tx fifo is full
          csr_spinwait(.ptr(ral.status.txfull), .exp_data(1'b0),
                       .timeout_ns(rd_txfifo_timeout_ns));
          `uvm_create_obj(i2c_item, item)
          item = read_txn_q.pop_front();
          `uvm_info("process_txq", $sformatf("send rdata:%x", item.wdata), UVM_MEDIUM)
          csr_wr(.ptr(ral.txdata), .value(item.wdata));
          read_size--;
        end
      end
    end
  endtask

  // Slow acq fifo read to create acq fifo full
  task process_slow_acq();
    uvm_reg_data_t read_data;
    i2c_item obs;
    bit is_read;
    bit acq_fifo_empty = 1;
    int delay;
    string id = "process_slow_acq";

    wait(cfg.sent_acq_cnt > 0);

    while (cfg.sent_acq_cnt != cfg.rcvd_acq_cnt ||
           acq_fifo_empty == 0) begin

      delay = $urandom_range(50, 100);

      // Assuming interval between each byte is 6.2us
      #(delay * 1us);

      // polling status.acqempty == 0
      csr_rd(.ptr(ral.status.acqempty), .value(acq_fifo_empty));

      if (!acq_fifo_empty) begin
        // read one entry and compare
        csr_rd(.ptr(ral.acqdata), .value(read_data));
        `uvm_info(id, $sformatf("acq data %x", read_data), UVM_MEDIUM)
        `uvm_create_obj(i2c_item, obs);
        obs = acq2item(read_data);
        obs.tran_id = cfg.rcvd_acq_cnt++;
        p_sequencer.target_mode_wr_obs_port.write(obs);
      end else begin // if (read_data == 0)
        cfg.clk_rst_vif.wait_clks(1);
        `uvm_info(id, $sformatf("acq_dbg: sent:%0d rcvd:%0d acq_is_empty",
                                           cfg.sent_acq_cnt, cfg.rcvd_acq_cnt), UVM_MEDIUM)
      end
    end // while (cfg.sent_acq_cnt != cfg.rcvd_acq_cnt ||...
    `uvm_info(id, "process_end", UVM_MEDIUM)
  endtask // process_slow_acq

  // Slow tx fifio write to create tx fifo empty
  task process_slow_txq();
    uvm_reg_data_t data;
    int read_size;
    int rd_txfifo_timeout_ns = 50_000;
    // indefinite time
    int tx_empty_timeout_ns = 500_000_000;
    int delay;
    string id = "process_slow_txq";

    wait(cfg.m_i2c_agent_cfg.sent_rd_byte > 0);

    while (cfg.m_i2c_agent_cfg.sent_rd_byte != cfg.m_i2c_agent_cfg.rcvd_rd_byte ||
           sent_txn_cnt < num_trans) begin
      cfg.clk_rst_vif.wait_clks(1);
      if (read_rcvd.size() > 0) begin
        read_size = read_rcvd.pop_front();
        `uvm_info(id, $sformatf("proc_txq read_size :%0d", read_size), UVM_HIGH)
      end

      while (read_size > 0) begin
        cfg.clk_rst_vif.wait_clks(1);
        if ($urandom_range(0, 1) < 1) begin
          // Wait for intr_state.tx_empty and clear.
          csr_spinwait(.ptr(ral.intr_state.tx_empty), .exp_data(1'b1),
                       .timeout_ns(tx_empty_timeout_ns));
          csr_wr(.ptr(ral.intr_state.tx_empty), .value(1'b1));
        end
        if (read_txn_q.size() > 0) begin
          i2c_item item;
          //check tx fifo is full
          csr_spinwait(.ptr(ral.status.txfull), .exp_data(1'b0),
                       .timeout_ns(rd_txfifo_timeout_ns));
          item = read_txn_q.pop_front();
          `uvm_info(id, $sformatf("send rdata:%x", item.wdata), UVM_MEDIUM)
          csr_wr(.ptr(ral.txdata), .value(item.wdata));
          read_size--;
        end
      end // while (read_size > 0)
    end // while (cfg.m_i2c_agent_cfg.sent_byte !=...
    `uvm_info(id, "proc_txq end", UVM_MEDIUM)
  endtask // process_slow_txq


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
        `uvm_info("seq", $sformatf("RS inserted before data %0d", i), UVM_MEDIUM)
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
  // TODO : target address will be randomly picked between target_addr0 nad target_addr1.
  virtual function void fetch_txn(ref i2c_item src_q[$], i2c_item dst_q[$]);
    i2c_item txn;
    i2c_item rs_txn;
    i2c_item exp_txn;
    i2c_item full_txn;
    int read_size;
    bit is_read = get_read_write();

    `uvm_info("seq", $sformatf("idx %0d:is_read:%0b size:%0d fetch_txn:%0d", start_cnt++, is_read,
                               src_q.size(), full_txn_num++), UVM_MEDIUM)
    print_wr_data(src_q);
    `uvm_create_obj(i2c_item, full_txn)

    // Add 'START' to the front
    `uvm_create_obj(i2c_item, txn)
    txn.drv_type = HostStart;
    dst_q.push_back(txn);
    full_txn.start = 1;
    if (is_read) full_txn.tran_id = this.exp_rd_id++;
    // Address
    `uvm_create_obj(i2c_item, txn)
    `uvm_create_obj(i2c_item, exp_txn)
    txn.drv_type = HostData;
    txn.start = 1;
    txn.wdata[7:1] = target_addr0;
    txn.wdata[0] = is_read;
    txn.tran_id = this.tran_id++;
    `downcast(exp_txn, txn.clone());
    dst_q.push_back(txn);
    full_txn.addr = txn.wdata[7:1];
    full_txn.read = is_read;

    p_sequencer.target_mode_wr_exp_port.write(exp_txn);
    cfg.sent_acq_cnt++;

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

      // RS creates 2 extra acq entry
      // one for RS
      // the other for a new start acq_entry with address
      if (txn.drv_type == HostRStart) begin
        bit prv_read = 0;
        `uvm_create_obj(i2c_item, exp_txn)
        exp_txn.drv_type = HostRStart;
        exp_txn.rstart = 1;
        exp_txn.tran_id = this.tran_id++;
        p_sequencer.target_mode_wr_exp_port.write(exp_txn);
        cfg.sent_acq_cnt++;
        `uvm_create_obj(i2c_item, rs_txn)
        `downcast(rs_txn, txn.clone())
        dst_q.push_back(txn);

        rs_txn.drv_type = HostData;
        rs_txn.start = 1;
        rs_txn.rstart = 0;
        rs_txn.wdata[7:1] = target_addr1;
        prv_read = is_read;
        is_read = rs_txn.read;
        rs_txn.wdata[0] = is_read;
        dst_q.push_back(rs_txn);
        // create a separate stat/addr entry for exp
        `uvm_create_obj(i2c_item, exp_txn)
        `downcast(exp_txn, rs_txn.clone());
        exp_txn.tran_id = this.tran_id++;
        p_sequencer.target_mode_wr_exp_port.write(exp_txn);
        cfg.sent_acq_cnt++;
        // fetch previous full_txn and creat a new one
        if (prv_read) begin
          full_txn.stop = 1;
          p_sequencer.target_mode_rd_exp_port.write(full_txn);
        end
        `uvm_create_obj(i2c_item, full_txn)
        `downcast(full_txn, rs_txn);
        if (is_read) begin
          full_txn.tran_id = exp_rd_id++;
        end
      end else begin
        if (is_read) begin
          i2c_item read_txn;
          `uvm_create_obj(i2c_item, read_txn)
          `downcast(read_txn, txn.clone())
          full_txn.num_data++;
          if (src_q.size() == 0) begin
            txn.drv_type = HostNAck;
          end else begin
            // if your next item is restart Do nack
            if (src_q[0].drv_type == HostRStart) txn.drv_type = HostNAck;
            else txn.drv_type = HostAck;
          end
          dst_q.push_back(txn);
          read_txn_q.push_back(read_txn);
        end else begin
          `downcast(exp_txn, txn.clone());
          // Add RS transaction to driver only
          // and create address transaction after
          dst_q.push_back(txn);
          exp_txn.tran_id = this.tran_id++;
          p_sequencer.target_mode_wr_exp_port.write(exp_txn);
          cfg.sent_acq_cnt++;
        end
      end
    end // while (src_q.size() > 0)

    // Stop
    `uvm_create_obj(i2c_item, txn)
    `uvm_create_obj(i2c_item, exp_txn)
    txn.tran_id = this.tran_id++;
    txn.stop = 1;
    txn.drv_type = HostStop;
    `downcast(exp_txn, txn.clone());
    dst_q.push_back(txn);
    full_txn.stop = 1;
    p_sequencer.target_mode_wr_exp_port.write(exp_txn);
    cfg.sent_acq_cnt++;
    if (is_read) begin
      p_sequencer.target_mode_rd_exp_port.write(full_txn);
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
endclass : i2c_base_vseq
