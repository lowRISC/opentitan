// Copyright lowRISC contributors (OpenTitan project).
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
  bit                                 inactive_level_en = 1'b0;

  // indicate channels are setup before enabled
  bit [NUM_PATTGEN_CHANNELS-1:0]      channel_setup = 'h0;
  bit [NUM_PATTGEN_CHANNELS-1:0]      channel_start = 'h0;
  // this one-hot vector is used for round-robin arbitrating the accesses to the shared registers
  // this vector is initialized to 1 (the channel 0 is granted by default)
  bit [NUM_PATTGEN_CHANNELS-1:0]      channel_grant = 'h1;

  // A constraint for the gaps between items in the sequence of pattgen commands
  int unsigned                        pattgen_max_dly = 5;

  // If this true then the sequence might inject errors in stop_pattgen_channels.
  bit                                 error_injected_enb = 1'b0;

  // constraints
  constraint num_trans_c {
    num_trans inside {[cfg.seq_cfg.pattgen_min_num_trans : cfg.seq_cfg.pattgen_max_num_trans]};
  }
  virtual task pre_start();
    cfg.m_pattgen_agent_cfg.en_monitor = cfg.en_scb;
    `uvm_info(`gfn, $sformatf("\n--> %s monitor and scoreboard",
        cfg.en_scb ? "enable" : "disable"), UVM_DEBUG)
    // env_cfg must be reset after vseq completion
    cfg.seq_cfg.pattgen_min_prediv = 0;
    cfg.seq_cfg.pattgen_min_len    = 0;
    cfg.seq_cfg.pattgen_min_reps   = 0;
    super.pre_start();
  endtask : pre_start

  // TODO: consider optimize the base_vseq to make each channel
  // cfg, start, stop independently with semaphore (PR #4040)
  virtual task body();
    `uvm_info(`gfn, "\n--> start of sequence", UVM_DEBUG)
    `uvm_info(`gfn, $sformatf("\n--> total required patterns %0d", num_trans), UVM_DEBUG)

    csr_wr(.ptr(ral.intr_enable), .value({TL_DW{1'b1}}));

    while (num_pattern_req < num_trans ||   // not send all pattern configs
           num_pattern_gen < num_trans ||   // not get  all pattern done interrupts
           channel_start) begin             // at least one channel is running
      wait(cfg.clk_rst_vif.rst_n); // wait until reset is de-asserted
      fork
        // all channels are completely independent (programm, start w/ or wo/ sync, and stop)
        setup_pattgen_channel(0);
        setup_pattgen_channel(1);
        start_pattgen_channels();
        stop_pattgen_channels();
      join
    end
    `uvm_info(`gfn, "\n--> end of sequence", UVM_DEBUG)
  endtask : body

  // Return the named register, but with a suffix to get the version for the requested channel.
  local function uvm_reg get_channel_reg(string name, int unsigned ch);
    uvm_reg r = ral.get_reg_by_name($sformatf("%s_ch%0d", name, ch));
    `DV_CHECK_FATAL(r !== null)
    return r;
  endfunction

  // Update the SIZE register as it applies to the requested channel (setting LEN_CH* and REPS_CH*)
  local task update_size_for_channel(int unsigned ch, int unsigned len, int unsigned reps);
    uvm_reg_field len_field = ral.size.get_field_by_name($sformatf("len_ch%0d", ch));
    uvm_reg_field reps_field = ral.size.get_field_by_name($sformatf("reps_ch%0d", ch));

    `DV_CHECK_FATAL(len_field !== null)
    `DV_CHECK_FATAL(reps_field !== null)

    len_field.set(len);
    reps_field.set(reps);
    csr_update(ral.size);
  endtask

  // Update the CTRL register to specify the polarity and inactive levels for the given channel
  // (setting INACTIVE_LEVEL_PCL_CH* and INACTIVE_LEVEL_PDA_CH*)
  local task update_ctrl_for_channel(int unsigned ch, bit polarity, bit pcl, bit pda);
    uvm_reg_field pol_fld = ral.ctrl.get_field_by_name($sformatf("polarity_ch%0d", ch));
    uvm_reg_field pcl_fld = ral.ctrl.get_field_by_name($sformatf("inactive_level_pcl_ch%0d", ch));
    uvm_reg_field pda_fld = ral.ctrl.get_field_by_name($sformatf("inactive_level_pcl_ch%0d", ch));

    `DV_CHECK_FATAL(pol_fld !== null)
    `DV_CHECK_FATAL(pcl_fld !== null)
    `DV_CHECK_FATAL(pda_fld !== null)

    pol_fld.set(polarity);
    pcl_fld.set(pcl);
    pda_fld.set(pda);

    csr_update(ral.ctrl);
  endtask

  // Write a PREDIV_CH* register to set the requested pre-divider
  local task write_prediv_for_channel(int unsigned ch, bit [31:0] value);
    csr_wr(.ptr(get_channel_reg("prediv", ch)), .value(value));
  endtask

  // Write the DATA_CH* multireg with the given pattern
  local task write_data_for_channel(int unsigned ch, bit [63:0] data);
    for (int unsigned i = 0; i < 2; i++) begin
      uvm_reg r = ral.get_reg_by_name($sformatf("data_ch%0d_%0d", ch, i));
      `DV_CHECK_FATAL(r !== null)
      csr_wr(.ptr(r), .value((data >> (32 * i)) & 32'hffffffff));
    end
  endtask

  // Set up the requested channel if this is a good time (there are still more patterns to request;
  // setup is granted; the channel is not yet set up; no other channel is running).
  local task setup_pattgen_channel(int unsigned ch);
    // If we have already requested enough patterns, there's nothing to do on the channel.
    if (num_pattern_req >= num_trans) return;

    // We can only do something if the channel's setup is granted but the channel has not yet been
    // programmed.
    if (!channel_grant[ch] || channel_setup[ch]) return;

    // We don't want to do something if another channel is running. (This avoids re-programming
    // registers)
    if (channel_start & ~(1 << ch)) return;

    // Wait to make sure that the channel isn't currently enabled
    wait_for_channel_ready(ch);

    // Pick a random configuration for the channel, storing it into channel_cfg
    channel_cfg[ch] = get_random_channel_config(.channel(ch));

    ral.size.get_field_by_name($sformatf("len_ch%0d", ch));

    // Now perform register writes to configure the channel as desired. Annoyingly, this always uses
    // registers or fields with the index in their name, so lots of the work is done by child tasks.
    update_size_for_channel(ch, channel_cfg[ch].len, channel_cfg[ch].reps);
    write_prediv_for_channel(ch, channel_cfg[ch].prediv);
    write_data_for_channel(ch, channel_cfg[ch].data);
    update_ctrl_for_channel(ch,
                            channel_cfg[ch].polarity,
                            channel_cfg[ch].inactive_level_pcl,
                            channel_cfg[ch].inactive_level_pda);

    update_pattgen_agent_cfg(.channel(ch));
    channel_setup[ch] = 1'b1;
    rol_grant();
  endtask

  // Wait a short time (up to pattgen_max_dly)
  //
  // Completes early on reset.
  local task short_delay();
    int unsigned dly;
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(dly, dly inside {[0:pattgen_max_dly]};)
    cfg.clk_rst_vif.wait_clks_or_rst(dly);
  endtask

  virtual task start_pattgen_channels();
    if (num_pattern_req < num_trans) begin
      if ($urandom_range(0, 99) < cfg.seq_cfg.pattgen_sync_channels_pct) begin
        // For some percentage of the time, we start all the channels at the same instant (ensuring
        // that they stay in sync)
        if (channel_setup[0] && !channel_start[0] && channel_setup[1] && !channel_start[1]) begin
          short_delay();
          control_channels(AllChannels, Enable);
          {channel_start[0], channel_start[1]} = {1'b1, 1'b1};
          `uvm_info(`gfn, "\n  all channels: activated", UVM_DEBUG)
        end
      end else begin
      // otherwise, activate channels independently
        for (uint i = 0; i < NUM_PATTGEN_CHANNELS; i++) begin
          if (channel_setup[i] && !channel_start[i]) begin
            channel_select_e ch_select;
            `downcast(ch_select, i+1)
            short_delay();
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
      if (error_injected_enb) begin
        if ($urandom_range(0, 99) < cfg.seq_cfg.error_injected_pct) begin
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
          if (!error_injected) cfg.m_pattgen_agent_cfg.channel_done = Channel0;
          clear_interrupts(Channel0, error_injected);
          control_channels(Channel0, Disable);
          if (error_injected) cfg.m_pattgen_agent_cfg.error_injected[0] = 1'b0;
          num_pattern_gen++;
          {channel_setup[0], channel_start[0]} = {1'b0, 1'b0};
          `uvm_info(`gfn, $sformatf("\n  channel 0: %s %0d/%0d",
              error_injected ? "error" : "completed", num_pattern_gen, num_trans), UVM_DEBUG)
        end
        Channel1: begin
          if (!error_injected) cfg.m_pattgen_agent_cfg.channel_done = Channel1;
          clear_interrupts(Channel1, error_injected);
          control_channels(Channel1, Disable);
          if (error_injected) cfg.m_pattgen_agent_cfg.error_injected[1] = 1'b0;
          num_pattern_gen++;
          {channel_setup[1], channel_start[1]} = {1'b0, 1'b0};
          `uvm_info(`gfn, $sformatf("\n  channel 1: %s %0d/%0d",
              error_injected ? "error" : "completed", num_pattern_gen, num_trans), UVM_DEBUG)
        end
        AllChannels: begin
          if (!error_injected) cfg.m_pattgen_agent_cfg.channel_done = AllChannels;
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
      cfg.m_pattgen_agent_cfg.channel_done = NoChannels;
    end
  endtask : stop_pattgen_channels

  // Wait (using multiple reads of the channel's enable register) until the requested channel is not
  // enabled.
  local task wait_for_channel_ready(int unsigned ch);
    uvm_reg_field fld = ral.ctrl.get_field_by_name($sformatf("enable_ch%0d", ch));
    `DV_CHECK_FATAL(fld != null)

    // Wait for at least one clock cycle so that the csr_update for the
    // channel setup don't happen in the same cycle. This avoids a warning in
    // VCS saying: Setting the value of field while containing register is
    // being accessed may result in loss of desired field value. A race
    // condition between threads concurrently accessing the register model is
    // the likely cause of the problem.
    cfg.clk_rst_vif.wait_clks(1);

    csr_spinwait(.ptr(fld), .exp_data(1'b0));
    `uvm_info(`gfn, $sformatf("\n  channel %0d is ready for programming", ch), UVM_DEBUG)
  endtask

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
              num_pattern_req - 1, num_trans, channel_cfg[0].convert2string()), UVM_DEBUG)
          `uvm_info(`gfn, $sformatf("\n  sync channel 1: request %0d/%0d\n%s",
              num_pattern_req, num_trans, channel_cfg[0].convert2string()), UVM_DEBUG)
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
      short_delay();
      csr_wr(.ptr(ral.intr_state), .value(intr_clear));
    end else begin
      `uvm_info(`gfn, $sformatf("\n  channel error, no clear interrupts %b", intr_clear), UVM_DEBUG)
    end
  endtask : clear_interrupts

  // this function randomizes the channel config
  virtual function pattgen_channel_cfg get_random_channel_config(uint channel);
    pattgen_channel_cfg ch_cfg;
    ch_cfg = pattgen_channel_cfg::type_id::create($sformatf("channel_cfg_%0d", channel));
    if (inactive_level_en) begin
      // TODO(#23219): Remove this when the scoreboard supports the inactive_level feature.
      ch_cfg.inactive_level_disabled_c.constraint_mode(0);
    end
    `DV_CHECK_RANDOMIZE_WITH_FATAL(ch_cfg,
      ch_cfg.polarity dist {
        1'b0 :/ cfg.seq_cfg.pattgen_low_polarity_pct,
        1'b1 :/ (100 - cfg.seq_cfg.pattgen_low_polarity_pct)
      };
      ch_cfg.data[31:0] dist {
        DataMax :/ cfg.seq_cfg.data_top_pct,
        DataMin :/ cfg.seq_cfg.data_bottom_pct,
        [DataMin + 1:DataMax - 1] :/ cfg.seq_cfg.data_middle_pct
      };
      ch_cfg.data[63:32] dist {
        DataMax :/ cfg.seq_cfg.data_top_pct,
        DataMin :/ cfg.seq_cfg.data_bottom_pct,
        [DataMin:DataMax] :/ cfg.seq_cfg.data_middle_pct
      };
      ch_cfg.prediv dist {
        cfg.seq_cfg.pattgen_max_prediv :/ cfg.seq_cfg.data_top_pct,
        cfg.seq_cfg.pattgen_min_prediv :/ cfg.seq_cfg.data_bottom_pct,
        [cfg.seq_cfg.pattgen_min_prediv + 1 :
         cfg.seq_cfg.pattgen_max_prediv - 1] :/ cfg.seq_cfg.data_middle_pct
      };
      ch_cfg.reps dist {
        cfg.seq_cfg.pattgen_max_reps :/ cfg.seq_cfg.data_top_pct,
        cfg.seq_cfg.pattgen_min_reps :/ cfg.seq_cfg.data_bottom_pct,
        [cfg.seq_cfg.pattgen_min_reps:cfg.seq_cfg.pattgen_max_reps] :/ cfg.seq_cfg.data_middle_pct
      };
      ch_cfg.len dist {
        cfg.seq_cfg.pattgen_max_len :/ cfg.seq_cfg.data_top_pct,
        cfg.seq_cfg.pattgen_min_len :/ cfg.seq_cfg.data_bottom_pct,
        [cfg.seq_cfg.pattgen_min_len:cfg.seq_cfg.pattgen_max_len] :/ cfg.seq_cfg.data_middle_pct
      };
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

  // Left rotate the one-hot channel_grant bitmask by one place
  local task rol_grant();
    channel_grant = {channel_grant[NUM_PATTGEN_CHANNELS-2:0],
                     channel_grant[NUM_PATTGEN_CHANNELS-1]};
  endtask

  task wait_host_for_idle();
    csr_spinwait(.ptr(ral.ctrl.enable_ch0),     .exp_data(1'b0));
    csr_spinwait(.ptr(ral.ctrl.enable_ch1),     .exp_data(1'b0));
    csr_spinwait(.ptr(ral.intr_state.done_ch0), .exp_data(1'b0));
    csr_spinwait(.ptr(ral.intr_state.done_ch1), .exp_data(1'b0));
  endtask : wait_host_for_idle

endclass : pattgen_base_vseq
