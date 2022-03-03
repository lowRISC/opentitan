// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class otbn_scoreboard extends cip_base_scoreboard #(
    .CFG_T(otbn_env_cfg),
    .RAL_T(otbn_reg_block),
    .COV_T(otbn_env_cov)
  );
  `uvm_component_utils(otbn_scoreboard)

  uvm_tlm_analysis_fifo #(otbn_model_item) model_fifo;
  uvm_tlm_analysis_fifo #(otbn_trace_item) trace_fifo;

  // Queues of trace items copied from the model_fifo and trace_fifo, respectively. These get paired
  // up in pop_trace_queues(). process_model_fifo and process_trace_fifo copy items from the
  // (blocking) FIFOs to the queues and then call pop_trace_queues(), which avoids having to poll
  // the (non-blocking) queues directly.
  otbn_model_item iss_trace_queue[$];
  otbn_trace_item rtl_trace_queue[$];

  // Each time we see a read on the A side, we set an entry in the exp_read_values associative
  // array. There are three situations that we need to deal with:
  //
  //   (1) A read from a register that can only be written by SW, so the RAL's mirrored value should
  //       already be right.
  //
  //   (2) A read from a register that can be updated by HW, but where we know what the value should
  //       be.
  //
  //   (3) A read from a register that can be updated by HW and where we have no idea what the value
  //       should be.
  //
  // To handle these three possibilities, we store a 34-bit otbn_exp_read_data_t value with fields
  // upd, chk and val. Here upd and chk are 1 bit each and val is 32 bits.
  //
  // If upd is false, we ignore the other fields and do not update the RAL's mirrored value.
  // Otherwise we update RAL's mirrored value to match the data from the D channel. If both upd and
  // chk are True, we raise an error if the data from the D channel doesn't match val.
  //
  // To connect up the A-side request with a subsequent D-side response, we use an associative
  // array, mapping the transaction source ID (a_source in the TL transaction) to an expected value.
  otbn_exp_read_data_t exp_read_values [tl_source_t];

  // A flag that tracks the fact that we've seen a TL write to the CMD register that we expect to
  // start OTBN. We track this because we derive the "start" signal in the model from an internal
  // DUT signal, so need to make sure it stays in sync with the TL side.
  //
  // If false, there are no transactions pending. This gets set in process_tl_addr when we see a
  // write to CMD. This runs on a posedge of the clock. We expect to see the model start on the
  // following negedge. When we process a change to model status that shows things starting (in
  // process_model_fifo), we check that the flag is set and then clear it. When setting the flag, we
  // queue a check to run on the following posedge of the clock to make sure the flag isn't still
  // set.
  bit pending_start_tl_trans = 1'b0;

  // The mirrored STATUS register from the ISS.
  bit [7:0] model_status = 8'd0;

  // The "locked" field is used to track whether OTBN is "locked". For most operational state
  // tracking, we go through the ISS, but OTBN can become locked without actually starting an
  // operation (for example, there might be a malformed TL transaction). We spot that sort of thing
  // here, updating the "locked" flag if either the ISS says to do so OR if we see something 'out of
  // band'.
  bit locked = 1'b0;

  // A counter for the number of fatal alerts that we've seen. This gets incremented by on_alert().
  int unsigned fatal_alert_count = 0;
  // A flag showing that we've seen a recoverable alert
  bit          recov_alert_seen  = 1'b0;

  // Flags saying that we expect alerts. These might be set (slightly) after an alert comes in and
  // that's ok. We'll marry up the flags and the alerts themselves in the check phase. The
  // *_alert_expected bits get cleared when we see the expected alert. The fatal_alert_allowed bit
  // gets set at the same time as fatal_alert_expected but is not cleared: this represents the fact
  // that fatal alerts are sent continuously.
  bit fatal_alert_expected = 1'b0;
  bit fatal_alert_allowed  = 1'b0;
  bit recov_alert_expected = 1'b0;

  // A counter giving how many "alert wait counters" are currently running. The scoreboard should
  // object to ending the run phase if this is nonzero.
  int unsigned num_alert_wait_counters = 0;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    model_fifo = new("model_fifo", this);
    trace_fifo = new("trace_fifo", this);

    // Disable alert checking in cip_base_scoreboard (we've got a different system set up which
    // handles the fact that we might not know that an alert should happen until after the fact).
    do_alert_check = 1'b0;
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    fork
      process_model_fifo();
      process_trace_fifo();
    join_none
  endtask

  virtual function void reset(string kind = "HARD");
    super.reset(kind);

    // Delete all the entries in exp_read_values: if there are D transactions pending after an A
    // transaction, the reset will have caused them to be forgotten.
    exp_read_values.delete();

    model_status = otbn_pkg::StatusIdle;
    pending_start_tl_trans = 1'b0;

    // Clear the locked bit (this is modelling RTL state that should be cleared on reset)
    locked = 1'b0;

    // Clear all alert counters and flags
    fatal_alert_count = 0;
    fatal_alert_expected = 1'b0;
    fatal_alert_allowed  = 1'b0;
    recov_alert_expected = 1'b0;

    // Reset any state tracking in the coverage collector
    if (cfg.en_cov) cov.on_reset();
  endfunction

  task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);
    case (channel)
      AddrChannel: process_tl_addr(item);
      DataChannel: process_tl_data(item);
      default: `uvm_fatal(`gfn, $sformatf("Invalid channel: %0h", channel))
    endcase
  endtask

  task process_tl_addr(tl_seq_item item);
    uvm_reg              csr;
    uvm_reg_addr_t       masked_addr, aligned_addr;
    operational_state_e  state;
    otbn_exp_read_data_t exp_read_data = '{upd: 1'b0, chk: 'x, val: 'x};

    state = cfg.controller_vif.get_operational_state();

    aligned_addr = ral.get_word_aligned_addr(item.a_addr);
    masked_addr  = aligned_addr & ral.get_addr_mask();

    // If coverage is enabled, track the write.
    if (cfg.en_cov) cov.on_tl_write(masked_addr, item.a_data, state);

    // Is this a write to memory (either DMEM or IMEM)?
    if (item.is_write()) begin
      uvm_mem mem = ral.default_map.get_mem_by_offset(aligned_addr);
      if (mem != null) begin
        uvm_reg_addr_t base = mem.get_offset(0, ral.default_map);
        `DV_CHECK_FATAL(base <= masked_addr)
        process_tl_mem_write(mem, masked_addr - base, item);
      end
    end

    csr = ral.default_map.get_reg_by_offset(aligned_addr);

    // csr might be null and that's ok (it just means an access to an unmapped register, which will
    // have no effect)
    if (csr == null)
      return;

    if (item.is_write()) begin
      // Track coverage for write accesses to external CSRs over TL-UL.
      if (cfg.en_cov) begin
        cov.on_ext_csr_access(csr, otbn_env_pkg::AccessSoftwareWrite, item.a_data, state);
      end

      // If this is a write, update the RAL model
      void'(csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask)));

      case (csr.get_name())
        // Spot writes to the "cmd" register that tell us to start
        "cmd": begin
          // We start any operation when we see a write of the related command and we are currently
          // in the IDLE operational state. See the comment above pending_start_tl_trans to see how
          // this tracking works.
          bit cmd_operation = item.a_data inside {otbn_pkg::CmdSecWipeImem,
                                                  otbn_pkg::CmdSecWipeDmem,
                                                  otbn_pkg::CmdExecute};
          if (cmd_operation && (model_status == otbn_pkg::StatusIdle)) begin
            // Set a flag: we're expecting the model to start on the next posedge. Also, spawn off a
            // checking thread that will make sure the flag has been cleared again by the following
            // posedge (or the one after that in the case of memory secure wipe operations).
            // Note that the reset() method is only called in the DV base class on the
            // following posedge of rst_n, so we have to check whether we're still in reset here.
            pending_start_tl_trans = 1'b1;
            fork begin
              repeat (2) @(cfg.clk_rst_vif.cb);
              `DV_CHECK_FATAL(!cfg.clk_rst_vif.rst_n || !pending_start_tl_trans,
                              "Model ignored a write of EXECUTE to the CMD register.")
            end
            join_none;
          end
        end
        "alert_test": begin
          if (item.is_write && (item.a_data[0])) begin
            expect_alert("fatal");
          end
          if (item.is_write && (item.a_data[1])) begin
            expect_alert("recov");
          end
        end
        default: begin
          // No other special behaviour for writes
        end
      endcase
      return;
    end

    // Otherwise, this is a read transaction. Fill in an otbn_exp_read_data_t struct appropriately.
    case (csr.get_name())
      "intr_state": begin
        // Interrupt state register.
        //
        // TODO: Track this more precisely. We know that it should latch !status.busy if intr_enable
        // is set.
        exp_read_data = '{upd: 1'b1, chk: 1'b0, val: 'x};
      end

      "status": begin
        // Status register. If we're locked, this should read 0xff. Otherwise, fall back to the
        // expected operational state (IDLE = 0; BUSY_EXECUTE = 1; BUSY_SEC_WIPE_DMEM = 2;
        // BUSY_SEC_WIPE_IMEM = 3).
        //
        // TODO: Track states other than IDLE and BUSY_EXECUTE.
        exp_read_data = '{upd: 1'b1, chk: 1'b1, val: locked ? 32'hff : model_status};
      end

      "err_bits": begin
        // Error bitfield
        //
        // TODO: Maybe this could be tracked more precisely. It should only update when an operation
        // finishes.
        exp_read_data = '{upd: 1'b1, chk: 1'b0, val: 'x};
      end

      "fatal_alert_cause": begin
        // Bitfield for the cause of a fatal alert
        //
        // TODO: Maybe this could be tracked more precisely. It should only update when a fatal
        // alert is signalled.
        exp_read_data = '{upd: 1'b1, chk: 1'b0, val: 'x};
      end

      "insn_cnt": begin
        // Instruction count
        //
        // TODO: Track this properly. We've got the magic number on the insn_cnt_if interface.
        exp_read_data = '{upd: 1'b1, chk: 1'b0, val: 'x};
      end

      default: begin
        // Other registers cannot be updated by the hardware, so don't need any special handling
        // here. The registers that aren't write-only are: intr_enable and cmd.
      end
    endcase

    // There shouldn't be an existing entry in exp_read_values for a_source: if there is, then the
    // host side must have sent two messages for the same source without waiting for a response,
    // violating the TL protocol.
    `DV_CHECK_FATAL(!exp_read_values.exists(item.a_source))

    exp_read_values[item.a_source] = exp_read_data;
  endtask

  task process_tl_data(tl_seq_item item);
    uvm_reg              csr;
    uvm_reg_addr_t       csr_addr;
    otbn_exp_read_data_t exp_read_data;

    // The data-channel response to a write is just an ack, which isn't particularly interesting.
    // Check for integrity errors (which should lock the block), but otherwise there's nothing to
    // do.
    if (item.is_write()) begin
      if (item.d_error) locked = 1'b1;
      return;
    end

    // We're also only interested in registers; the scoreboard doesn't explicitly model memories in
    // the RAL. Look to see if this is a valid register address. If not, it was to a memory and we
    // can ignore it.
    csr_addr = ral.get_word_aligned_addr(item.a_addr);
    csr = ral.default_map.get_reg_by_offset(csr_addr);
    if (csr == null)
      return;

    // Track coverage for read accesses through the bus to external CSRs.
    if (cfg.en_cov) begin
      cov.on_ext_csr_access(csr, otbn_env_pkg::AccessSoftwareRead, item.d_data,
                            cfg.controller_vif.get_operational_state());
    end

    // Look up the expected read data for item and then clear it (to get a quick error if something
    // has come unstuck and we see two replies for a single addr + source combo)
    `DV_CHECK_FATAL(exp_read_values.exists(item.a_source))
    exp_read_data = exp_read_values[item.a_source];
    exp_read_values.delete(item.a_source);

    if (exp_read_data.upd) begin
      if (exp_read_data.chk) begin
        // This is a value that can be written by HW, but we think we know what the value should be
        `DV_CHECK_EQ(item.d_data, exp_read_data.val,
                     $sformatf("value for register %0s", csr.get_full_name()))
      end
      // Update the RAL model to match the value we've just read from HW
      void'(csr.predict(.value(item.d_data), .kind(UVM_PREDICT_READ)));
    end else begin
      // We don't predict any sort of hardware backdoor updates to this register so the mirrored
      // value in the RAL should be correct. Is it?
      `DV_CHECK_EQ(item.d_data, csr.get_mirrored_value(),
                   $sformatf("value for auto-predicted register %0s", csr.get_full_name()))
    end
  endtask

  // Called on each write to memory (on the A side). This is responsible for updating the model of
  // the CRC register.
  function void process_tl_mem_write(uvm_mem mem, bit [31:0] offset, tl_seq_item item);
    bit            is_imem;
    logic [14:0]   mem_idx;
    logic [47:0]   crc_item;
    uvm_reg_data_t old_crc;
    bit [31:0]     new_crc;

    // Ignore any partial or misaligned writes: these don't update the CRC.
    if ((item.a_addr & 3) || (item.a_size != 2))
      return;

    // Build the 48-bit value that's supposed to be added to the CRC. This is built as the triple
    // {imem, idx, wdata}, where imem is a 1-bit value showing whether this is IMEM, idx is the
    // index of the 32-bit word in memory, zero-extended to 15 bits, and wdata is the 32-bit word
    // that was written.
    is_imem = mem.get_name() == "imem";
    mem_idx = offset >> 2;
    crc_item = {is_imem, mem_idx, item.a_data};
    `uvm_info(`gfn,
              $sformatf("Updating CRC with memory write: {%0d, 0x%0h, 0x%0h} = 0x%012h",
                        is_imem, mem_idx, item.a_data, crc_item),
              UVM_HIGH);
    `DV_CHECK_FATAL(!$isunknown(crc_item))

    // Grab the old modelled CRC value (which we store in the RAL as the predicted value for
    // LOAD_CHECKSUM). This should be a 32-bit number and shouldn't have any unknown bits.
    old_crc = ral.load_checksum.checksum.get_mirrored_value();
    `DV_CHECK_FATAL(old_crc >> 32 == 0)
    `DV_CHECK_FATAL(!$isunknown(old_crc))

    new_crc = cfg.model_agent_cfg.vif.step_crc(crc_item, old_crc);

    `uvm_info(`gfn,
              $sformatf("CRC step: 0x%08h -> 0x%08h (or 0x%08h -> 0x%08h)",
                        old_crc, new_crc, old_crc ^ {32{1'b1}}, new_crc ^ {32{1'b1}}),
              UVM_HIGH);

    if (cfg.en_cov) begin
      cov.on_mem_write(mem, offset, item.a_data, cfg.controller_vif.get_operational_state());
    end

    // Predict the resulting value of LOAD_CHECKSUM
    `DV_CHECK_FATAL(ral.load_checksum.checksum.predict(.value(new_crc), .kind(UVM_PREDICT_READ)))
  endfunction

  task process_model_fifo();
    otbn_model_item item;

    forever begin
      model_fifo.get(item);
      `uvm_info(`gfn, $sformatf("received model transaction:\n%0s", item.sprint()), UVM_HIGH)

      case (item.item_type)
        OtbnModelStatus: begin
          bit was_running = model_status inside {otbn_pkg::StatusBusyExecute,
                                                 otbn_pkg::StatusBusySecWipeDmem,
                                                 otbn_pkg::StatusBusySecWipeImem};
          bit is_running = item.status inside {otbn_pkg::StatusBusyExecute,
                                               otbn_pkg::StatusBusySecWipeDmem,
                                               otbn_pkg::StatusBusySecWipeImem};

          // Has the status changed from idle to busy? If so, we should have seen a write to the
          // command register on the previous posedge. See comment above pending_start_tl_trans for
          // the details.
          if (model_status == otbn_pkg::StatusIdle && is_running) begin
            `DV_CHECK_FATAL(pending_start_tl_trans,
                            "Saw start transaction without corresponding write to CMD")
            pending_start_tl_trans = 1'b0;
          end

          // Has the status changed to locked? This should be accompanied by a fatal alert
          if (item.status == otbn_pkg::StatusLocked) begin
            expect_alert("fatal");
          end
          // Has the status changed from busy to idle with a nonzero err_bits? If so, we should see
          // a recoverable alert.
          if (was_running && item.status == otbn_pkg::StatusIdle && item.err_bits != 0) begin
            expect_alert("recov");
          end

          model_status = item.status;

          if (cfg.en_cov) cov.on_state_change(model_status);
        end

        OtbnModelInsn: begin
          // The model agent's monitor should be configured to only emit OtbnModelInsn items if
          // coverage is enabled.
          `DV_CHECK_FATAL(cfg.en_cov)
          // We don't expect any instructions unless we're currently running something.
          `DV_CHECK_EQ_FATAL(model_status, 1 /* BUSY_EXECUTE */,
                             "Saw instruction when not in BUSY_EXECUTE operational state.")

          iss_trace_queue.push_back(item);
          pop_trace_queues();
        end

        default: `uvm_fatal(`gfn, $sformatf("Bad item type %0d", item.item_type))
      endcase
    end
  endtask

  task process_trace_fifo();
    otbn_trace_item item;
    forever begin
      trace_fifo.get(item);

      // The trace monitor should be configured to only emit items if coverage is enabled. Here, we
      // wait on trace_fifo either way, to avoid a massive memory leak if something comes unstuck.
      // However, we check that we were actually expecting things if anything comes through.
      `DV_CHECK_FATAL(cfg.en_cov)

      rtl_trace_queue.push_back(item);
      pop_trace_queues();
    end
  endtask

  // Pop from iss_trace_queue and rtl_trace_queue while they both contain an entry
  function void pop_trace_queues();
    while ((iss_trace_queue.size() > 0) && (rtl_trace_queue.size() > 0)) begin
      otbn_model_item iss_item = iss_trace_queue.pop_front();
      otbn_trace_item rtl_item = rtl_trace_queue.pop_front();
      cov.on_insn(iss_item, rtl_item);
    end
  endfunction

  // Wait up to max_wait cycles for us to decide that we should be expecting the named alert. While
  // this is running, num_alert_wait_counters will be positive which should mean that we object to
  // end of the run phase.
  protected task wait_for_expected_alert(string alert_name, int unsigned max_wait);
    bit expected = 1'b0;

    num_alert_wait_counters++;
    for (int unsigned i = 0; i < max_wait; i++) begin
      // Note that if we're waiting for a status change that implies a recoverable alert, we'll also
      // accept one that implies a fatal alert. The reason is that you can trigger a recoverable
      // alert and then, on the next cycle, a fatal alert. You'll only see one status change (from
      // busy to locked), so the scoreboard has no way of knowing whether the recoverable alert was
      // supposed to have happened. In practice, I suspect we don't care: if a fatal alert was
      // raised, a recoverable alert doesn't really matter.
      expected = ((alert_name == "recov") && recov_alert_expected) || fatal_alert_allowed;
      if (expected || cfg.under_reset) begin
        break;
      end
      @(cfg.clk_rst_vif.cb);
    end
    num_alert_wait_counters--;

    if (cfg.under_reset) begin
      // If we're in reset, exit immediately. No need to check anything or update any state
      return;
    end

    if (!expected) begin
      `uvm_fatal(`gfn,
                 $sformatf({"A %0s alert arrived %0d cycles ago and ",
                            "we still don't think it should have done."},
                           alert_name, max_wait))
    end

    if (alert_name == "fatal") begin
      // If this is a fatal alert, check the counter is positive (otherwise something has gone really
      // wrong), but leave it unchanged.
      `DV_CHECK_FATAL((fatal_alert_count > 0) && fatal_alert_allowed)
    end else begin
      // Otherwise this was a recoverable alert. Check that the seen flag is set (this should have
      // happened just before we were originally called) and then wait a cycle of the other clock
      // before clearing it. This extra cycle is to allow the wait_for_alert() task which should be
      // running at the same time to see the flag set.
      `DV_CHECK_FATAL(recov_alert_seen)
      @(cfg.m_alert_agent_cfg[alert_name].vif.receiver_cb);
      recov_alert_seen = 1'b0;
    end
  endtask

  // Wait up to max_wait cycles on the alert interface for the named alert. While this is running,
  // num_alert_wait_counters will be positive which should mean that we object to end of the run
  // phase.
  protected task wait_for_alert(string alert_name, int unsigned max_wait);
    bit seen = 1'b0;

    num_alert_wait_counters++;
    for (int unsigned i = 0; i < max_wait; i++) begin
      seen = (alert_name == "recov") ? recov_alert_seen : (fatal_alert_count > 0);
      if (seen || cfg.under_reset) begin
        break;
      end
      @(cfg.m_alert_agent_cfg[alert_name].vif.receiver_cb);
    end
    num_alert_wait_counters--;

    if (cfg.under_reset) begin
      // If we're in reset, exit immediately. No need to check anything or update any state
      return;
    end

    if (!seen) begin
      `uvm_fatal(`gfn,
                 $sformatf({"We saw a STATUS change %0d cycles ago that implied we'd ",
                            "get a %0s alert but it still hasn't arrived."},
                           max_wait, alert_name))
    end

    if (alert_name == "fatal") begin
      // If this was a fatal alert then check the counter is positive and that the expected flag is
      // set. Clear the "expected" flag, but not "allowed" (so that we won't see a problem when the
      // fatal alert is re-triggered).
      `DV_CHECK_FATAL((fatal_alert_count > 0) && fatal_alert_expected)
      fatal_alert_expected = 1'b0;
    end else begin
      // Otherwise this was a recoverable alert. Check that the expected flag is set and then wait a
      // cycle of the other clock before clearing it (to allow the wait_for_expected_alert() task
      // that should be running at the same time to see it set).
      `DV_CHECK_FATAL(recov_alert_expected)
      @(cfg.clk_rst_vif.cb);
      recov_alert_expected = 1'b0;
    end
  endtask

  // Overridden from cip_base_scoreboard. Called when an alert happens.
  function void on_alert(string alert_name, alert_esc_agent_pkg::alert_esc_seq_item item);

    `uvm_info(`gfn, $sformatf("on_alert(%0s)", alert_name), UVM_HIGH)

    // An alert has just come in. Increment counter / set flag showing that it has been seen.
    if (alert_name == "fatal") begin
      fatal_alert_count += 1;
    end else if (alert_name == "recov") begin
      // We're not supposed to see a second recoverable alert while we're still "waiting to expect"
      // the previous one. If that happens then recov_alert_seen will be set.
      `DV_CHECK_FATAL(!recov_alert_seen, "Double recoverable alert seen")
      recov_alert_seen = 1'b1;
    end
    else `uvm_fatal(`gfn, $sformatf("Bad alert name: %0s", alert_name));

    // Wait up to 10 cycles for the a prediction to come through (giving up on reset). Note that
    // this might be here already, in which case wait_for_expected_alert will take zero time
    fork
      wait_for_expected_alert(alert_name, 10);
    join_none
  endfunction

  // Called when we see something that makes us think an alert should happen
  protected function void expect_alert(string alert_name);
    int unsigned max_delay;

    `uvm_info(`gfn, $sformatf("expect_alert(%0s)", alert_name), UVM_HIGH)

    if (alert_name == "fatal") begin
      fatal_alert_expected = 1'b1;
      fatal_alert_allowed  = 1'b1;
    end else if (alert_name == "recov") begin
      // We're not supposed to see an event that expects a second recoverable alert while we're
      // still waiting for the previous one to arrive. If that happens then recov_alert_expected
      // will be set.
      `DV_CHECK_FATAL(!recov_alert_expected, "Double recoverable alert expect with no alert")
      recov_alert_expected = 1'b1;
    end
    else `uvm_fatal(`gfn, $sformatf("Bad alert name: %0s", alert_name));

    // Otherwise, we haven't seen the corresponding alert yet. Wait for a bit on the (slower) alert
    // interface clock for the alert to come through, giving up on reset. The wait is calculated as
    //
    //    ack_delay_max +
    //    ack_stable_max +
    //    arbitrary delay for alert_p to go down +
    //    2 cycles of main clock
    //
    // We model the 3rd and 4th term as 10 slow clock cycles in total, giving:
    max_delay = (cfg.m_alert_agent_cfg[alert_name].ack_delay_max +
                 cfg.m_alert_agent_cfg[alert_name].ack_stable_max +
                 10);
    fork
      wait_for_alert(alert_name, max_delay);
    join_none
  endfunction

  virtual function void phase_ready_to_end(uvm_phase phase);
    if (phase.get_name() != "run") return;

    // We cannot end while num_alert_wait_counters is positive (which means that wait_for_alert
    // and/or wait_for_expected_alert are running). Wait until they are finished to make sure that
    // we don't fail to notice a missing (or unjustified) alert.
    if (num_alert_wait_counters != 0) begin
      phase.raise_objection(this, "num_alert_wait_counters != 0");
      fork
        begin
          wait (num_alert_wait_counters == 0);
          phase.drop_objection(this);
        end
      join_none
    end
  endfunction

endclass
