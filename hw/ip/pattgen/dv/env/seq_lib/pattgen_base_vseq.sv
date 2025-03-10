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

  // A count of how many patterns have been requested so far
  uint                                num_pattern_req = 0;

  // A count of how many patterns have been generated so far
  uint                                num_pattern_gen = 0;

  // Configuration for each of the channels
  rand pattgen_channel_cfg            channel_cfg[NUM_PATTGEN_CHANNELS-1:0];

  // If set, remove a constraint that forces the inactive level feature to be disabled.
  bit                                 inactive_level_en = 1'b0;

  // A bitmask that shows which channels have been set up.
  bit [NUM_PATTGEN_CHANNELS-1:0]      channel_setup = 'h0;

  // A bitmask that shows which channels have been enabled.
  bit [NUM_PATTGEN_CHANNELS-1:0]      channel_start = 'h0;

  // This one-hot vector is used for round-robin arbitrating accesses to the shared registers. It is
  // initialized to 1 (the channel 0 is granted by default)
  bit [NUM_PATTGEN_CHANNELS-1:0]      channel_grant = 'h1;

  // A constraint for the gaps between items in the sequence of pattgen commands
  int unsigned                        pattgen_max_dly = 5;

  // If this true then the sequence might inject errors in stop_pattgen_channels.
  bit                                 error_injected_enb = 1'b0;

  // constraints
  constraint num_trans_c {
    num_trans inside {[cfg.seq_cfg.pattgen_min_num_trans : cfg.seq_cfg.pattgen_max_num_trans]};
  }

  // Code that runs before pre_body. (A task from uvm_sequence_base)
  extern virtual task pre_start();

  // The body of the sequence. (A task from uvm_sequence_base)
  extern virtual task body();

  // Return the named register, but with a suffix to get the version for the requested channel.
  extern local function uvm_reg get_channel_reg(string name, int unsigned ch);

  // Update the SIZE register as it applies to the requested channel (setting LEN_CH* and REPS_CH*)
  extern local task update_size_for_channel(int unsigned ch, int unsigned len, int unsigned reps);

  // Update the CTRL register to specify the polarity and inactive levels for the given channel
  // (setting INACTIVE_LEVEL_PCL_CH* and INACTIVE_LEVEL_PDA_CH*)
  extern local task update_ctrl_for_channel(int unsigned ch, bit polarity, bit pcl, bit pda);

  // Write a PREDIV_CH* register to set the requested pre-divider
  extern local task write_prediv_for_channel(int unsigned ch, bit [31:0] value);

  // Write the DATA_CH* multireg with the given pattern
  extern local task write_data_for_channel(int unsigned ch, bit [63:0] data);

  // Set up the requested channel if this is a good time (there are still more patterns to request;
  // setup is granted; the channel is not yet set up; no other channel is running).
  extern local task setup_pattgen_channel(int unsigned ch);

  // Wait a short time (up to pattgen_max_dly)
  //
  // Completes early on reset.
  extern local task short_delay();

  // Start the channels that have been set up but not yet started. Potentially wait until all
  // channels have been set up and then start them all at once.
  extern local task start_pattgen_channels();

  // Look at the interrupt status bits to see which channels have completed. For each of these
  // channels, clear the local channel_setup and channel_start flags, resetting the model of the
  // channel to the "ready" state.
  extern local task stop_pattgen_channels();

  // Wait (using multiple reads of the channel's enable register) until the requested channel is not
  // enabled.
  extern local task wait_for_channel_ready(int unsigned ch);

  // A masked write to the channel enable fields. Set the status in the RAL for the channels that
  // are true in the mask to match the status argument.
  extern function void add_desired_enables(bit [NUM_PATTGEN_CHANNELS-1:0] mask,
                                           channel_status_e status);

  // Update all the channels selected by mask with the enable status in the status argument.
  extern local task control_channels(bit [NUM_PATTGEN_CHANNELS-1:0] mask, channel_status_e status);

  // Write a bitmask of the channels that have stopped and generated an interrupt to the intr_bits
  // output argument.
  extern local task get_interrupt_status(output bit[NUM_PATTGEN_CHANNELS-1:0] intr_bits);

  // Clear the interrupts for all selected channels
  extern local task clear_interrupts(bit [NUM_PATTGEN_CHANNELS-1:0] mask);

  // Return a randomised channel configuration. The channel index argument is just used to construct
  // the name of the object.
  extern protected virtual function pattgen_channel_cfg get_random_channel_config(uint channel);

  // Update m_pattgen_agent_cfg for the given channel, based on channel_cfg[channel].
  extern local function void update_pattgen_agent_cfg(int channel);

  // Left rotate the one-hot channel_grant bitmask by one place
  extern local task rol_grant();

  // Wait until neither channel is enabled and both have triggered the done interrupt.
  extern protected task wait_host_for_idle();
endclass

task pattgen_base_vseq::pre_start();
  cfg.m_pattgen_agent_cfg.en_monitor = cfg.en_scb;
  `uvm_info(`gfn, $sformatf("\n--> %s monitor and scoreboard",
                            cfg.en_scb ? "enable" : "disable"), UVM_DEBUG)
  // env_cfg must be reset after vseq completion
  cfg.seq_cfg.pattgen_min_prediv = 0;
  cfg.seq_cfg.pattgen_min_len    = 0;
  cfg.seq_cfg.pattgen_min_reps   = 0;
  super.pre_start();
endtask

// TODO: consider optimize the base_vseq to make each channel
// cfg, start, stop independently with semaphore (PR #4040)
task pattgen_base_vseq::body();
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
endtask

function uvm_reg pattgen_base_vseq::get_channel_reg(string name, int unsigned ch);
  uvm_reg r = ral.get_reg_by_name($sformatf("%s_ch%0d", name, ch));
  `DV_CHECK_FATAL(r !== null)
  return r;
endfunction

task pattgen_base_vseq::update_size_for_channel(int unsigned ch,
                                                int unsigned len,
                                                int unsigned reps);
  uvm_reg_field len_field = ral.size.get_field_by_name($sformatf("len_ch%0d", ch));
  uvm_reg_field reps_field = ral.size.get_field_by_name($sformatf("reps_ch%0d", ch));

  `DV_CHECK_FATAL(len_field !== null)
  `DV_CHECK_FATAL(reps_field !== null)

  len_field.set(len);
  reps_field.set(reps);
  csr_update(ral.size);
endtask

task pattgen_base_vseq::update_ctrl_for_channel(int unsigned ch, bit polarity, bit pcl, bit pda);
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

task pattgen_base_vseq::write_prediv_for_channel(int unsigned ch, bit [31:0] value);
  csr_wr(.ptr(get_channel_reg("prediv", ch)), .value(value));
endtask

task pattgen_base_vseq::write_data_for_channel(int unsigned ch, bit [63:0] data);
  for (int unsigned i = 0; i < 2; i++) begin
    uvm_reg r = ral.get_reg_by_name($sformatf("data_ch%0d_%0d", ch, i));
    `DV_CHECK_FATAL(r !== null)
    csr_wr(.ptr(r), .value((data >> (32 * i)) & 32'hffffffff));
  end
endtask

task pattgen_base_vseq::setup_pattgen_channel(int unsigned ch);
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

task pattgen_base_vseq::short_delay();
  int unsigned dly;
  `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(dly, dly inside {[0:pattgen_max_dly]};)
  cfg.clk_rst_vif.wait_clks_or_rst(dly);
endtask

task pattgen_base_vseq::start_pattgen_channels();
  if (num_pattern_req < num_trans) begin
    if ($urandom_range(0, 99) < cfg.seq_cfg.pattgen_sync_channels_pct) begin
      // For some percentage of the time, we start all the channels at the same instant (ensuring
      // that they stay in sync)
      if (channel_setup[0] && !channel_start[0] && channel_setup[1] && !channel_start[1]) begin
        short_delay();
        control_channels(2'b11, Enable);
        {channel_start[0], channel_start[1]} = {1'b1, 1'b1};
        `uvm_info(`gfn, "\n  all channels: activated", UVM_DEBUG)
      end
    end else begin
    // otherwise, activate channels independently
      for (uint i = 0; i < NUM_PATTGEN_CHANNELS; i++) begin
        if (channel_setup[i] && !channel_start[i]) begin
          short_delay();
          control_channels(1 << i, Enable);
          channel_start[i]= 1'b1;
          `uvm_info(`gfn, $sformatf("\n  channel %0d: activated", i), UVM_DEBUG)
        end
      end
    end
  end
endtask

task pattgen_base_vseq::stop_pattgen_channels();
  bit error_injected;
  bit [NUM_PATTGEN_CHANNELS-1:0] intr_status;
  bit [NUM_PATTGEN_CHANNELS-1:0] channel_stop;

  if (channel_start) begin
    error_injected = 1'b0;
    get_interrupt_status(intr_status);
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
      2'b00: begin
        // If no channels have stopped yet and we don't want to inject an error by stopping one
        // early then there is nothing to do.
      end
      2'b01: begin
        if (!error_injected) begin
          cfg.m_pattgen_agent_cfg.channel_done = 2'b01;
          clear_interrupts(2'b01);
        end
        control_channels(2'b01, Disable);
        if (error_injected) cfg.m_pattgen_agent_cfg.error_injected[0] = 1'b0;
        num_pattern_gen++;
        {channel_setup[0], channel_start[0]} = {1'b0, 1'b0};
        `uvm_info(`gfn, $sformatf("\n  channel 0: %s %0d/%0d",
            error_injected ? "error" : "completed", num_pattern_gen, num_trans), UVM_DEBUG)
      end
      2'b10: begin
        if (!error_injected) begin
          cfg.m_pattgen_agent_cfg.channel_done = 2'b10;
          clear_interrupts(2'b10);
        end
        control_channels(2'b10, Disable);
        if (error_injected) cfg.m_pattgen_agent_cfg.error_injected[1] = 1'b0;
        num_pattern_gen++;
        {channel_setup[1], channel_start[1]} = {1'b0, 1'b0};
        `uvm_info(`gfn, $sformatf("\n  channel 1: %s %0d/%0d",
            error_injected ? "error" : "completed", num_pattern_gen, num_trans), UVM_DEBUG)
      end
      2'b11: begin
        if (!error_injected) begin
          cfg.m_pattgen_agent_cfg.channel_done = 2'b11;
          clear_interrupts(2'b11);
        end
        control_channels(2'b11, Disable);
        if (error_injected) begin
          cfg.m_pattgen_agent_cfg.error_injected = 2'b00;
          `uvm_info(`gfn, $sformatf("\n  update m_pattgen_agent_cfg.error_injected"), UVM_DEBUG)
        end
        num_pattern_gen += 2;
        channel_setup = {NUM_PATTGEN_CHANNELS{1'b0}};
        channel_start = {NUM_PATTGEN_CHANNELS{1'b0}};
        `uvm_info(`gfn, $sformatf("\n  all channels: %s %0d/%0d",
            error_injected ? "error" : "completed", num_pattern_gen, num_trans), UVM_DEBUG)
      end
      default: `uvm_fatal(`gfn, $sformatf("unknown value for channel_stop: 0x%0h", channel_stop))
    endcase
    cfg.m_pattgen_agent_cfg.channel_done = 2'b00;
  end
endtask

task pattgen_base_vseq::wait_for_channel_ready(int unsigned ch);
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

function void pattgen_base_vseq::add_desired_enables(bit [NUM_PATTGEN_CHANNELS-1:0] mask,
                                                     channel_status_e status);
  for (int unsigned ch = 0; ch < NUM_PATTGEN_CHANNELS; ch++) begin
    if (mask[ch]) begin
      uvm_reg_field len_field = ral.ctrl.get_field_by_name($sformatf("enable_ch%0d", ch));
      `DV_CHECK_FATAL(len_field != null)
      len_field.set(status);
    end
  end
endfunction

task pattgen_base_vseq::control_channels(bit [NUM_PATTGEN_CHANNELS-1:0] mask,
                                         channel_status_e               status);
  string                         verb;
  int unsigned                   counter;

  // wait for no register access on bus before enable channels to avoid the race condition (i.e.
  // concurrent access to update ctrl.polarity on the other channel)
  wait_no_outstanding_access();

  add_desired_enables(mask, status);

  if (status == Enable) begin
    for (int unsigned i = 0; i < NUM_PATTGEN_CHANNELS; i++) begin
      if (mask[i]) begin
        num_pattern_req++;
        `uvm_info(`gfn,
                  $sformatf("\n  channel %0d: request %0d/%0d\n%s",
                            i, num_pattern_req, num_trans, channel_cfg[i].convert2string()),
                  UVM_DEBUG)
      end
    end
  end

  `uvm_info(`gfn,
            $sformatf("\n  %s %0d/%0d patterns",
                      (status == Enable) ? "requested" : "received",
                      (status == Enable) ? num_pattern_req : num_pattern_gen,
                      num_trans),
            UVM_DEBUG)

  csr_update(ral.ctrl);
endtask

task pattgen_base_vseq::get_interrupt_status(output bit[NUM_PATTGEN_CHANNELS-1:0] intr_bits);
  bit [TL_DW-1:0] intr_state;
  csr_rd(.ptr(ral.intr_state), .value(intr_state));
  intr_bits = NUM_PATTGEN_CHANNELS'(intr_state);
  `uvm_info(`gfn, $sformatf("\n  intr_state %b", intr_bits), UVM_DEBUG)
endtask

task pattgen_base_vseq::clear_interrupts(bit [NUM_PATTGEN_CHANNELS-1:0] mask);
  short_delay();
  csr_wr(.ptr(ral.intr_state), .value(mask));
endtask

function pattgen_channel_cfg pattgen_base_vseq::get_random_channel_config(uint channel);
  pattgen_channel_cfg ch_cfg;
  ch_cfg = pattgen_channel_cfg::type_id::create($sformatf("channel_cfg_%0d", channel));
  if (inactive_level_en) begin
    // TODO(#23219): Remove this when the scoreboard supports the inactive_level feature.
    ch_cfg.inactive_level_disabled_c.constraint_mode(0);
  end
  `DV_CHECK_RANDOMIZE_WITH_FATAL(ch_cfg,
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
endfunction

function void pattgen_base_vseq::update_pattgen_agent_cfg(int channel);
  cfg.m_pattgen_agent_cfg.polarity[channel] = channel_cfg[channel].polarity;
  // see the specification document, the effective values of prediv, len, and reps
  // are incremented from the coresponding register values
  cfg.m_pattgen_agent_cfg.length[channel]   = (channel_cfg[channel].len + 1) *
                                              (channel_cfg[channel].reps + 1);
  `uvm_info(`gfn, $sformatf("\n--> pattgen_agent_cfg: channel %0d, polarity %0b, length %0d",
      channel, cfg.m_pattgen_agent_cfg.polarity[channel],
      cfg.m_pattgen_agent_cfg.length[channel]), UVM_DEBUG)
endfunction

task pattgen_base_vseq::rol_grant();
  channel_grant = {channel_grant[NUM_PATTGEN_CHANNELS-2:0], channel_grant[NUM_PATTGEN_CHANNELS-1]};
endtask

task pattgen_base_vseq::wait_host_for_idle();
  csr_spinwait(.ptr(ral.ctrl.enable_ch0),     .exp_data(1'b0));
  csr_spinwait(.ptr(ral.ctrl.enable_ch1),     .exp_data(1'b0));
  csr_spinwait(.ptr(ral.intr_state.done_ch0), .exp_data(1'b0));
  csr_spinwait(.ptr(ral.intr_state.done_ch1), .exp_data(1'b0));
endtask
