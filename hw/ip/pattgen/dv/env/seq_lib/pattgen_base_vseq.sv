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
  uint                     num_pattern_req = 0;
  uint                     num_pattern_gen = 0;
  // channel config
  rand pattgen_channel_cfg channel_cfg[NUM_PATTGEN_CHANNELS-1:0];

  // indicate channels are setup before enabled
  bit [NUM_PATTGEN_CHANNELS-1:0] ch_under_setup = 'h0;
  bit [NUM_PATTGEN_CHANNELS-1:0] ch_under_start = 'h0;
  // this one-hot vector is used for round-robin arbitrating the accesses to the shared registers
  // this vector is initialized to 1 (the channel 0 is granted by default)
  bit [NUM_PATTGEN_CHANNELS-1:0] ch_grant_setup = 'h1;

  // random variables
  rand uint                num_runs;    // TODO: this variable is reserved for V2 tests
  rand uint                stop_channel_dly;
  // if sync_all_channels bit is set: both channels can start simmultaneously
  rand bit                 sync_all_channels;

  // constraints
  constraint num_trans_c {
    num_trans inside {[cfg.seq_cfg.pattgen_min_num_trans : cfg.seq_cfg.pattgen_max_num_trans]};
  }
  constraint num_runs_c {
    num_runs inside {[cfg.seq_cfg.pattgen_min_num_runs : cfg.seq_cfg.pattgen_max_num_runs]};
  }
  constraint sync_all_channels_c {
    sync_all_channels dist {
      1'b1 :/ cfg.seq_cfg.pattgen_sync_channels_pct,
      1'b0 :/ (100 - cfg.seq_cfg.pattgen_sync_channels_pct)
    };
  }
  constraint stop_channel_dly_c {
    stop_channel_dly inside {[cfg.seq_cfg.pattgen_min_dly : cfg.seq_cfg.pattgen_max_dly]};
  }

  task pre_start();
    num_runs.rand_mode(0);
    cfg.m_pattgen_agent_cfg.en_monitor = cfg.en_scb;
    // set time to stop test
    cfg.m_pattgen_agent_cfg.ok_to_end_delay_ns = cfg.ok_to_end_delay_ns;
    `uvm_info(`gfn, $sformatf("\n--> %s monitor and scoreboard",
        cfg.en_scb ? "enable" : "disable"), UVM_DEBUG)
    super.pre_start();
  endtask : pre_start

  // setup basic pattgen features
  virtual task initialize_dut();
    csr_wr(.csr(ral.ctrl),        .value({TL_DW{1'b0}}));
    csr_wr(.csr(ral.intr_enable), .value({TL_DW{1'b1}}));
    csr_wr(.csr(ral.intr_state),  .value({TL_DW{1'b0}}));
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
           ch_under_start) begin            // at least one channel is running
      fork
        // all channels are completely independent (programm, start w/ or wo/ sync, and stop)
        setup_pattgen_channel_0();
        setup_pattgen_channel_1();
        start_pattgen_channels();
        stop_pattgen_channels();
      join
    end
    `uvm_info(`gfn, $sformatf("\n--> ch_under_setup %b", ch_under_setup), UVM_DEBUG)
    `uvm_info(`gfn, $sformatf("\n--> ch_under_start %b", ch_under_start), UVM_DEBUG)
    `uvm_info(`gfn, "\n--> end of sequence", UVM_DEBUG)
  endtask : body

  // TODO: can setup_pattgen_channel task be parameterized?
  // e.g. index the regster groups of channels before entering while-loop in body task
  virtual task setup_pattgen_channel_0();
    if (num_pattern_req < num_trans &&
         ch_grant_setup[0] &&       // ch0 setup is granted
        !ch_under_setup[0] &&       // ch0 has not been programmed
        !ch_under_start[1]) begin   // ch1 is not under start (avoid re-programming regs)
      channel_cfg[0] = get_random_channel_config(.channel(0));
      update_pattgen_agent_cfg(.channel(0));
      ral.size.len_ch0.set(channel_cfg[0].len);
      ral.size.reps_ch0.set(channel_cfg[0].reps);
      csr_update(ral.size);
      csr_wr(.csr(ral.prediv_ch0), .value(channel_cfg[0].prediv));
      csr_wr(.csr(ral.data_ch0_0), .value(channel_cfg[0].data[31:0]));
      csr_wr(.csr(ral.data_ch0_1), .value(channel_cfg[0].data[63:32]));
      ral.ctrl.polarity_ch0.set(channel_cfg[0].polarity);
      csr_update(ral.ctrl);
      ch_under_setup[0] = 1'b1;
      void'(right_rotation(ch_grant_setup));
      `uvm_info(`gfn, "\n  channel 0 is programmed", UVM_DEBUG)
    end
  endtask : setup_pattgen_channel_0

  virtual task setup_pattgen_channel_1();
    if (num_pattern_req < num_trans &&
        ch_grant_setup[1]  &&       // ch1 setup is granted
        !ch_under_setup[1] &&       // ch1 has not been programmed
        !ch_under_start[0]) begin   // ch0 is not under start (avoid re-programming regs)
      channel_cfg[1] = get_random_channel_config(.channel(1));
      update_pattgen_agent_cfg(.channel(1));
      ral.size.len_ch1.set(channel_cfg[1].len);
      ral.size.reps_ch1.set(channel_cfg[1].reps);
      csr_update(ral.size);
      csr_wr(.csr(ral.prediv_ch1), .value(channel_cfg[1].prediv));
      csr_wr(.csr(ral.data_ch1_0), .value(channel_cfg[1].data[31:0]));
      csr_wr(.csr(ral.data_ch1_1), .value(channel_cfg[1].data[63:32]));
      ral.ctrl.polarity_ch1.set(channel_cfg[1].polarity);
      csr_update(ral.ctrl);
      ch_under_setup[1] = 1'b1;
      void'(right_rotation(ch_grant_setup));
      `uvm_info(`gfn, "\n  channel 1 is programmed", UVM_DEBUG)
    end
  endtask : setup_pattgen_channel_1

  virtual task start_pattgen_channels();
    if (num_pattern_req < num_trans) begin
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(sync_all_channels)
      // if sync_all_channels is set, then activate both channels if they are setup and not busy
      if (sync_all_channels) begin
        // once sync_all_channels is set, temporaly disable its randomization to sync all channels
        sync_all_channels.rand_mode(0);
        if (ch_under_setup[0] && !ch_under_start[0] && ch_under_setup[1] && !ch_under_start[1]) begin
          {ch_under_start[0], ch_under_start[1]} = {1'b1, 1'b1};
          control_channels(AllChannels, Enable);
          `uvm_info(`gfn, "\n  all channels: activated", UVM_DEBUG)
          // re-enable sync_all_channels's randomization after all channels have been started
          sync_all_channels.rand_mode(1);
        end
      end else begin
      // otherwise, activate channels independently
        for (uint i = 0; i < NUM_PATTGEN_CHANNELS; i++) begin
          if (ch_under_setup[i] && !ch_under_start[i]) begin
            channel_select_e ch_select;
            `downcast(ch_select, i+1)
            ch_under_start[i]= 1'b1;
            control_channels(ch_select, Enable);
            `uvm_info(`gfn, $sformatf("\n  channel %0d: activated", i), UVM_DEBUG)
          end
        end
      end
    end
  endtask : start_pattgen_channels

  // this task allows channels to be stopped independently/simultaneously
  virtual task stop_pattgen_channels();
    bit [TL_DW-1:0] intr_state;

    if (ch_under_start) begin
      csr_rd(.ptr(ral.intr_state), .value(intr_state));
      case ({intr_state[DoneCh1], intr_state[DoneCh0]})
        Channel0: begin
          control_channels(Channel0, Disable);
          clear_interrupts(Channel0);
          num_pattern_gen++;
          `uvm_info(`gfn, $sformatf("\n  channel 0: completed %0d/%0d",
              num_pattern_gen, num_trans), UVM_DEBUG)
          {ch_under_setup[0], ch_under_start[0]} = {1'b0, 1'b0};
        end
        Channel1: begin
          control_channels(Channel1, Disable);
          clear_interrupts(Channel1);
          num_pattern_gen++;
          {ch_under_setup[1], ch_under_start[1]} = {1'b0, 1'b0};
          `uvm_info(`gfn, $sformatf("\n  channel 1: completed %0d/%0d",
              num_pattern_gen, num_trans), UVM_DEBUG)
        end
        AllChannels: begin
          control_channels(AllChannels, Disable);
          clear_interrupts(AllChannels);
          num_pattern_gen += 2;
          ch_under_setup = {NUM_PATTGEN_CHANNELS{1'b0}};
          ch_under_start = {NUM_PATTGEN_CHANNELS{1'b0}};
          `uvm_info(`gfn, $sformatf("\n  all channel: completed %0d/%0d",
              num_pattern_gen, num_trans), UVM_DEBUG)
        end
      endcase
    end
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(stop_channel_dly)
    cfg.clk_rst_vif.wait_clks(stop_channel_dly);
  endtask: stop_pattgen_channels

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
          channel_cfg[0].print_config($sformatf("\n  channel 0: request %0d/%0d",
              num_pattern_req, num_trans));
        end
      end
      Channel1: begin
        ral.ctrl.enable_ch1.set(status);
        if (status == Enable) begin
          num_pattern_req++;
          channel_cfg[1].print_config($sformatf("\n  channel 1: request %0d/%0d",
              num_pattern_req, num_trans));
        end
      end
      AllChannels: begin
        ral.ctrl.enable_ch0.set(status);
        ral.ctrl.enable_ch1.set(status);
        if (status == Enable) begin
          num_pattern_req += 2;
          channel_cfg[0].print_config($sformatf("\n  sync channel 0: request %0d/%0d",
              num_pattern_req - 1, num_trans));
          channel_cfg[1].print_config($sformatf("\n  sync channel 1: request %0d/%0d",
              num_pattern_req, num_trans));
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

  // this task allows the interrupts of channels to be cleared independently/simultaneously
  virtual task clear_interrupts(channel_select_e ch_select);
    bit [TL_DW-1:0] intr_clear;
    
    case (ch_select)
      Channel0:    intr_clear = 1 << DoneCh0;
      Channel1:    intr_clear = 1 << DoneCh1;
      AllChannels: intr_clear = (1 << DoneCh1) | (1 << DoneCh0);
      default:     `uvm_fatal(`gfn, "  invalid argument")
    endcase
    csr_wr(.csr(ral.intr_state), .value(intr_clear));
  endtask : clear_interrupts

  // this function randomizes the channel config
  function pattgen_channel_cfg get_random_channel_config(uint channel);
    pattgen_channel_cfg ch_cfg;
    ch_cfg = pattgen_channel_cfg::type_id::create($sformatf("channel_cfg_%0d", channel));
    `DV_CHECK_RANDOMIZE_WITH_FATAL(ch_cfg,
      ch_cfg.polarity dist {
        1'b0 :/ cfg.seq_cfg.pattgen_polarity_pct,
        1'b1 :/ (100 - cfg.seq_cfg.pattgen_polarity_pct)
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

endclass : pattgen_base_vseq
