// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class pattgen_base_vseq extends cip_base_vseq #(
    .RAL_T               (pattgen_reg_block),
    .CFG_T               (pattgen_env_cfg),
    .COV_T               (pattgen_env_cov),
    .VIRTUAL_SEQUENCER_T (pattgen_virtual_sequencer)
  );
  `uvm_object_utils(pattgen_base_vseq)
  `uvm_object_new

  // variables
  uint                                num_pattern_req = 0;
  uint                                num_pattern_gen = 0;
  // channel config
  rand pattgen_channel_cfg            channel_cfg[NUM_PATTGEN_CHANNELS-1:0];

  // indicate channels are setup before enabled
  bit [NUM_PATTGEN_CHANNELS-1:0]      channel_setup = 'h0;
  bit [NUM_PATTGEN_CHANNELS-1:0]      channel_start = 'h0;
  // this one-hot vector is used for round-robin arbitrating the accesses to the shared registers
  // this vector is initialized to 1 (the channel 0 is granted by default)
  bit [NUM_PATTGEN_CHANNELS-1:0]      channel_grant = 'h1;

  // random variables
  rand uint                           num_runs;
  rand uint                           b2b_pattern_dly;
  rand uint                           clear_intr_dly;
  // if start_all_channels bit is set: both channels can start simmultaneously
  rand bit                            start_all_channels;
  rand bit                            do_error_injected;
  rand bit [NUM_PATTGEN_CHANNELS-1:0] reset_channels;

  // constraints
  constraint num_trans_c {
    num_trans inside {[cfg.seq_cfg.pattgen_min_num_trans : cfg.seq_cfg.pattgen_max_num_trans]};
  }
  constraint num_runs_c {
    num_runs inside {[cfg.seq_cfg.pattgen_min_num_runs : cfg.seq_cfg.pattgen_max_num_runs]};
  }
  constraint start_all_channels_c {
    start_all_channels dist {
      1'b1 :/ cfg.seq_cfg.pattgen_sync_channels_pct,
      1'b0 :/ (100 - cfg.seq_cfg.pattgen_sync_channels_pct)
    };
  }
  constraint do_error_injected_c {
    do_error_injected dist {
      1'b1:/ cfg.seq_cfg.error_injected_pct,
      1'b0:/ (100 - cfg.seq_cfg.error_injected_pct)
    };
  }
  constraint b2b_pattern_dly_c {
    b2b_pattern_dly inside {[cfg.seq_cfg.pattgen_min_dly : cfg.seq_cfg.pattgen_max_dly]};
  }
  constraint clear_intr_dly_c {
    clear_intr_dly inside {[cfg.seq_cfg.pattgen_min_dly : cfg.seq_cfg.pattgen_max_dly]};
  }

  virtual task pre_start();
    cfg.m_pattgen_agent_cfg.en_monitor = cfg.en_scb;
    `uvm_info(`gfn, $sformatf("\n--> %s monitor and scoreboard",
        cfg.en_scb ? "enable" : "disable"), UVM_DEBUG)
    super.pre_start();
  endtask : pre_start

  virtual task post_start();
    // env_cfg must be reset after vseq completion
    cfg.seq_cfg.error_injected_enb = 1'b0;
    cfg.seq_cfg.pattgen_min_prediv = 0;
    cfg.seq_cfg.pattgen_min_len    = 0;
    cfg.seq_cfg.pattgen_min_reps   = 0;
    super.post_start();
  endtask : post_start

  // setup basic pattgen features
  virtual task initialize_dut();
    csr_wr(.csr(ral.intr_enable), .value({TL_DW{1'b1}}));
    `uvm_info(`gfn, "\n  call pattgen_init", UVM_DEBUG)
  endtask : initialize_dut

  // TODO: consider optimize the base_vseq to make each channel
  // cfg, start, stop independently with semaphore (PR #4040)
  virtual task body();
    `uvm_info(`gfn, "\n--> start of sequence", UVM_DEBUG)
    `uvm_info(`gfn, $sformatf("\n--> total required patterns %0d", num_trans), UVM_DEBUG)

    initialize_dut();
    while (num_pattern_req < num_trans ||   // not send all pattern configs
           num_pattern_gen < num_trans ||   // not get  all pattern done interrupts
           channel_start) begin             // at least one channel is running
      fork
        // all channels are completely independent (programm, start w/ or wo/ sync, and stop)
        setup_pattgen_channel_0();
        setup_pattgen_channel_1();
        start_pattgen_channels();
        stop_pattgen_channels();
      join
    end
    `uvm_info(`gfn, $sformatf("\n--> channel_setup %b", channel_setup), UVM_DEBUG)
    `uvm_info(`gfn, $sformatf("\n--> channel_start %b", channel_start), UVM_DEBUG)
    `uvm_info(`gfn, "\n--> end of sequence", UVM_DEBUG)
  endtask : body

  // TODO: can setup_pattgen_channel task be parameterized?
  // e.g. index the regster groups of channels before entering while-loop in body task
  virtual task setup_pattgen_channel_0();
    if (num_pattern_req < num_trans &&
         channel_grant[0] &&       // ch0 setup is granted
        !channel_setup[0] &&       // ch0 has not been programmed
        !channel_start[1]) begin   // ch1 is not under start (avoid re-programming regs)
      wait_for_channel_ready(Channel0);
      channel_cfg[0] = get_random_channel_config(.channel(0));
      ral.size.len_ch0.set(channel_cfg[0].len);
      ral.size.reps_ch0.set(channel_cfg[0].reps);
      csr_update(ral.size);
      csr_wr(.csr(ral.prediv_ch0), .value(channel_cfg[0].prediv));
      csr_wr(.csr(ral.data_ch0_0), .value(channel_cfg[0].data[31:0]));
      csr_wr(.csr(ral.data_ch0_1), .value(channel_cfg[0].data[63:32]));
      ral.ctrl.polarity_ch0.set(channel_cfg[0].polarity);
      update_pattgen_agent_cfg(.channel(0));
      csr_update(ral.ctrl);
      channel_setup[0] = 1'b1;
      void'(right_rotation(channel_grant));
      `uvm_info(`gfn, "\n  channel 0: programmed", UVM_DEBUG)
    end
  endtask : setup_pattgen_channel_0

  virtual task setup_pattgen_channel_1();
    if (num_pattern_req < num_trans &&
        channel_grant[1]  &&       // ch1 setup is granted
        !channel_setup[1] &&       // ch1 has not been programmed
        !channel_start[0]) begin   // ch0 is not under start (avoid re-programming regs)
      wait_for_channel_ready(Channel1);
      channel_cfg[1] = get_random_channel_config(.channel(1));
      ral.size.len_ch1.set(channel_cfg[1].len);
      ral.size.reps_ch1.set(channel_cfg[1].reps);
      csr_update(ral.size);
      csr_wr(.csr(ral.prediv_ch1), .value(channel_cfg[1].prediv));
      csr_wr(.csr(ral.data_ch1_0), .value(channel_cfg[1].data[31:0]));
      csr_wr(.csr(ral.data_ch1_1), .value(channel_cfg[1].data[63:32]));
      ral.ctrl.polarity_ch1.set(channel_cfg[1].polarity);
      update_pattgen_agent_cfg(.channel(1));
      csr_update(ral.ctrl);
      channel_setup[1] = 1'b1;
      void'(right_rotation(channel_grant));
      `uvm_info(`gfn, "\n  channel 1: programmed", UVM_DEBUG)
    end
  endtask : setup_pattgen_channel_1

  virtual task start_pattgen_channels();
    if (num_pattern_req < num_trans) begin
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(start_all_channels)
      // if start_all_channels is set, then activate both channels if they are setup and not busy
      if (start_all_channels) begin
        // once start_all_channels is set, temporaly disable its randomization to sync all channels
        start_all_channels.rand_mode(0);
        if (channel_setup[0] && !channel_start[0] && channel_setup[1] && !channel_start[1]) begin
          `DV_CHECK_MEMBER_RANDOMIZE_FATAL(b2b_pattern_dly)
          cfg.clk_rst_vif.wait_clks(b2b_pattern_dly);
          control_channels(AllChannels, Enable);
          {channel_start[0], channel_start[1]} = {1'b1, 1'b1};
          `uvm_info(`gfn, "\n  all channels: activated", UVM_DEBUG)
          // re-enable start_all_channels's randomization after all channels have been started
          start_all_channels.rand_mode(1);
        end
      end else begin
      // otherwise, activate channels independently
        for (uint i = 0; i < NUM_PATTGEN_CHANNELS; i++) begin
          if (channel_setup[i] && !channel_start[i]) begin
            channel_select_e ch_select;
            `downcast(ch_select, i+1)
            `DV_CHECK_MEMBER_RANDOMIZE_FATAL(b2b_pattern_dly)
            cfg.clk_rst_vif.wait_clks(b2b_pattern_dly);
            control_channels(ch_select, Enable);
            channel_start[i]= 1'b1;
            `uvm_info(`gfn, $sformatf("\n  channel %0d: activated", i), UVM_DEBUG)
          end
        end
      end
    end
  endtask : start_pattgen_channels

  // this task allows channels to be stopped independently/simultaneously
  virtual task stop_pattgen_channels();
    bit error_injected;
    bit [NUM_PATTGEN_CHANNELS-1:0] intr_status;
    bit [NUM_PATTGEN_CHANNELS-1:0] channel_stop;

    if (channel_start) begin
      error_injected = 1'b0;
      get_interrupt_states(intr_status);
      //--------------------------------------------------------------------------------
      // inject error
      //--------------------------------------------------------------------------------
      // ch_start  intr_status   ch_stop   description
      //--------------------------------------------------------------------------------
      // 01 (CH0)  01            01        CH0 finished          CH1 not started
      // 01 (CH0)  00            01        CH0 error injected*   CH1 not started
      // 10 (CH1)  10            10        CH0 not started       CH1 finished
      // 10 (CH1)  00            10        CH0 not started       CH1 error injected*
      // 11 (CH1)  01            01        CH0 finished          CH1 error injected*
      // 11 (CH1)  10            10        CH0 error injected*   CH1 finished
      // 11 (CH1)  11            11        CH0 finished          CH1 finished
      // 11 (CH1)  00            11        CH0 error injected    CH1 error injected*
      channel_stop = intr_status; // default setting
      if (cfg.seq_cfg.error_injected_enb) begin
        `DV_CHECK_MEMBER_RANDOMIZE_FATAL(do_error_injected)
        if (do_error_injected) begin
          if (intr_status != channel_start) begin
            channel_stop = channel_start;
            error_injected = 1'b1;
            cfg.m_pattgen_agent_cfg.error_injected = channel_stop;
            `uvm_info(`gfn, $sformatf("\n  error inject: intr_status %b ch_stop %b ch_start %b",
                intr_status, channel_stop, channel_start), UVM_DEBUG)
          end
        end
      end

      case (channel_stop)
        Channel0: begin
          clear_interrupts(Channel0, error_injected);
          control_channels(Channel0, Disable);
          if (error_injected) cfg.m_pattgen_agent_cfg.error_injected[0] = 1'b0;
          num_pattern_gen++;
          {channel_setup[0], channel_start[0]} = {1'b0, 1'b0};
          `uvm_info(`gfn, $sformatf("\n  channel 0: %s %0d/%0d",
              error_injected ? "error" : "completed", num_pattern_gen, num_trans), UVM_DEBUG)
        end
        Channel1: begin
          clear_interrupts(Channel1, error_injected);
          control_channels(Channel1, Disable);
          if (error_injected) cfg.m_pattgen_agent_cfg.error_injected[1] = 1'b0;
          num_pattern_gen++;
          {channel_setup[1], channel_start[1]} = {1'b0, 1'b0};
          `uvm_info(`gfn, $sformatf("\n  channel 1: %s %0d/%0d",
              error_injected ? "error" : "completed", num_pattern_gen, num_trans), UVM_DEBUG)
        end
        AllChannels: begin
          clear_interrupts(AllChannels, error_injected);
          control_channels(AllChannels, Disable);
          if (error_injected) begin
            cfg.m_pattgen_agent_cfg.error_injected = NoChannels;
            `uvm_info(`gfn, $sformatf("\n  update m_pattgen_agent_cfg.error_injected"), UVM_DEBUG)
          end
          num_pattern_gen += 2;
          channel_setup = {NUM_PATTGEN_CHANNELS{1'b0}};
          channel_start = {NUM_PATTGEN_CHANNELS{1'b0}};
          `uvm_info(`gfn, $sformatf("\n  all channels: %s %0d/%0d",
              error_injected ? "error" : "completed", num_pattern_gen, num_trans), UVM_DEBUG)
        end
      endcase
    end
  endtask : stop_pattgen_channels

  virtual task wait_for_channel_ready(channel_select_e ch_select);
    case (ch_select)
      Channel0: begin
        csr_spinwait(.ptr(ral.ctrl.enable_ch0), .exp_data(1'b0));
        `uvm_info(`gfn, $sformatf("\n  channel 0 is ready for programmed"), UVM_DEBUG)
      end
      Channel1: begin
        csr_spinwait(.ptr(ral.ctrl.enable_ch1), .exp_data(1'b0));
        `uvm_info(`gfn, $sformatf("\n  channel 1 is ready for programmed"), UVM_DEBUG)
      end
    endcase
  endtask : wait_for_channel_ready

  // this task allows channels to be activated or stopped independently/simultaneously
  virtual task control_channels(channel_select_e ch_select, channel_status_e status);
    // wait for no register access on bus before enable channels to avoid the race condition
    // (i.e. concurrent access to update ctrl.polarity on the other channel)
    wait_no_outstanding_access();
    case (ch_select)
      Channel0: begin
        ral.ctrl.enable_ch0.set(status);
        if (status == Enable) begin
          num_pattern_req++;
          `uvm_info(`gfn, $sformatf("\n  channel 0: request %0d/%0d\n%s",
              num_pattern_req, num_trans, channel_cfg[0].convert2string()), UVM_DEBUG)
        end
      end
      Channel1: begin
        ral.ctrl.enable_ch1.set(status);
        if (status == Enable) begin
          num_pattern_req++;
          `uvm_info(`gfn, $sformatf("\n  channel 1: request %0d/%0d\n%s",
              num_pattern_req, num_trans, channel_cfg[1].convert2string()), UVM_DEBUG)
        end
      end
      AllChannels: begin
        ral.ctrl.enable_ch0.set(status);
        ral.ctrl.enable_ch1.set(status);
        if (status == Enable) begin
          num_pattern_req += 2;
          `uvm_info(`gfn, $sformatf("\n  sync channel 0: request %0d/%0d\n%s",
              num_pattern_req - 1, num_trans, channel_cfg[0].convert2string()), UVM_DEBUG);
          `uvm_info(`gfn, $sformatf("\n  sync channel 1: request %0d/%0d\n%s",
              num_pattern_req, num_trans, channel_cfg[1].convert2string()), UVM_DEBUG);
        end
      end
    endcase
    if (status == Enable) begin
      `uvm_info(`gfn, $sformatf("\n  requested %0d/%0d patterns",
          num_pattern_req, num_trans), UVM_DEBUG)
    end else begin
      `uvm_info(`gfn, $sformatf("\n  received %0d/%0d patterns",
          num_pattern_gen, num_trans), UVM_DEBUG)
    end
    csr_update(ral.ctrl);
  endtask : control_channels

  virtual task get_interrupt_states(output bit[NUM_PATTGEN_CHANNELS-1:0] intr_bits);
    bit [TL_DW-1:0] intr_state;
    csr_rd(.ptr(ral.intr_state), .value(intr_state));
    intr_bits = NUM_PATTGEN_CHANNELS'(intr_state);
    `uvm_info(`gfn, $sformatf("\n  intr_state %b", intr_bits), UVM_DEBUG)
  endtask : get_interrupt_states

  // this task allows the interrupts of channels to be cleared independently/simultaneously
  virtual task clear_interrupts(channel_select_e ch_select, bit error = 1'b0);
    bit [TL_DW-1:0] intr_clear ='h0;

    if (!error) begin
      case (ch_select)
        Channel0:    intr_clear = 1 << DoneCh0;
        Channel1:    intr_clear = 1 << DoneCh1;
        AllChannels: intr_clear = (1 << DoneCh1) | (1 << DoneCh0);
        default:     `uvm_fatal(`gfn, "  invalid argument")
      endcase
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(clear_intr_dly)
      cfg.clk_rst_vif.wait_clks(clear_intr_dly);
      csr_wr(.csr(ral.intr_state), .value(intr_clear));
    end else begin
      `uvm_info(`gfn, $sformatf("\n  channel error, no clear interrupts %b", intr_clear), UVM_DEBUG)
    end
  endtask : clear_interrupts

  // this function randomizes the channel config
  virtual function pattgen_channel_cfg get_random_channel_config(uint channel);
    pattgen_channel_cfg ch_cfg;
    ch_cfg = pattgen_channel_cfg::type_id::create($sformatf("channel_cfg_%0d", channel));
    `DV_CHECK_RANDOMIZE_WITH_FATAL(ch_cfg,
      ch_cfg.polarity dist {
        1'b0 :/ cfg.seq_cfg.pattgen_low_polarity_pct,
        1'b1 :/ (100 - cfg.seq_cfg.pattgen_low_polarity_pct)
      };
      ch_cfg.prediv inside {[cfg.seq_cfg.pattgen_min_prediv : cfg.seq_cfg.pattgen_max_prediv]};
      ch_cfg.len    inside {[cfg.seq_cfg.pattgen_min_len    : cfg.seq_cfg.pattgen_max_len]};
      ch_cfg.reps   inside {[cfg.seq_cfg.pattgen_min_reps   : cfg.seq_cfg.pattgen_max_reps]};
      solve ch_cfg.len before ch_cfg.data;
      ch_cfg.data   inside {[0 : (1 << (ch_cfg.len + 1)) - 1]};
    )
    return ch_cfg;
  endfunction : get_random_channel_config

  // this function allows update the pattgen_agent_config
  virtual function void update_pattgen_agent_cfg(int channel);
    cfg.m_pattgen_agent_cfg.polarity[channel] = channel_cfg[channel].polarity;
    // see the specification document, the effective values of prediv, len, and reps
    // are incremented from the coresponding register values
    cfg.m_pattgen_agent_cfg.length[channel]   = (channel_cfg[channel].len + 1) *
                                                (channel_cfg[channel].reps + 1);
    `uvm_info(`gfn, $sformatf("\n--> pattgen_agent_cfg: channel %0d, polarity %0b, length %0d",
        channel, cfg.m_pattgen_agent_cfg.polarity[channel],
        cfg.m_pattgen_agent_cfg.length[channel]), UVM_DEBUG)
  endfunction : update_pattgen_agent_cfg

  // right rotate a one-hot vector
  virtual function right_rotation(ref bit [NUM_PATTGEN_CHANNELS-1:0] x);
    x = {x[NUM_PATTGEN_CHANNELS-2:0], x[NUM_PATTGEN_CHANNELS-1]};
  endfunction : right_rotation

  // TODO: this task is reserved for the next PR
  task wait_host_for_idle();
    csr_spinwait(.ptr(ral.ctrl.enable_ch0),     .exp_data(1'b0));
    csr_spinwait(.ptr(ral.ctrl.enable_ch1),     .exp_data(1'b0));
    csr_spinwait(.ptr(ral.intr_state.done_ch0), .exp_data(1'b0));
    csr_spinwait(.ptr(ral.intr_state.done_ch1), .exp_data(1'b0));
  endtask : wait_host_for_idle

endclass : pattgen_base_vseq
