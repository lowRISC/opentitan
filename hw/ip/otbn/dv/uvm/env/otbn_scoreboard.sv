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

  bit saw_start_tl_trans = 1'b0;
  bit waiting_for_model = 1'b0;

  // The "running" field uses the OtbnModelStart and OtbnModelDone items on the model FIFO to track
  // whether we think OTBN is running at the moment. We know that this is in sync with the RTL
  // because of the MatchingDone_A assertion at testbench level.
  bit running = 1'b0;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    model_fifo = new("model_fifo", this);
    trace_fifo = new("trace_fifo", this);
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    fork
      process_model_fifo();
      process_trace_fifo();
      check_start();
    join_none
  endtask

  virtual function void reset(string kind = "HARD");
    super.reset(kind);

    // Delete all the entries in exp_read_values: if there are D transactions pending after an A
    // transaction, the reset will have caused them to be forgotten.
    exp_read_values.delete();

    // Clear waiting_for_model. This handles a corner case where a TL transaction comes in to start
    // OTBN just before a reset and the reset hits after the negedge of the clock (so we have set
    // waiting_for_model) but before the following clock cycle (which would have generated the
    // OtbnModelStart transaction).
    waiting_for_model = 1'b0;

    // Clear saw_start_tl_trans. Any "start" TL transaction will have been discarded by the reset,
    // so we shouldn't still be tracking it.
    saw_start_tl_trans = 1'b0;
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
    uvm_reg_addr_t       csr_addr;
    otbn_exp_read_data_t exp_read_data = '{upd: 1'b0, chk: 'x, val: 'x};

    csr_addr = ral.get_word_aligned_addr(item.a_addr);
    csr = ral.default_map.get_reg_by_offset(csr_addr);

    // csr might be null and that's ok (it's probably a write to memory).
    if (csr == null)
      return;

    if (item.is_write()) begin
      // If this is a write, update the RAL model
      void'(csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask)));

      // Track coverage for write accesses to external CSRs over TL-UL.
      if (cfg.en_cov) begin
        cov.on_ext_csr_access(csr, otbn_env_pkg::AccessSoftwareWrite, item.a_data,
                              cfg.controller_vif.get_operational_state());
      end

      case (csr.get_name())
        // Spot writes to the "cmd" register, which tell us to start
        // These start the processor. We don't pass those to the model through UVM, because it's
        // difficult to get the timing right (you only recognise the transaction on the clock edge
        // after you needed to set the signal!), so the testbench actually grabs the model's start
        // signal from the DUT internals. Of course, we need to check this is true exactly when we
        // expect it to be. Here, we set a flag to say that we expect the "start" signal to be high.
        // See the check_start() task, which checks it's true at the right time.
        "cmd": begin
          // We start the execution when we see a write of the EXECUTE command.
          if (item.a_data == otbn_pkg::CmdExecute) begin
            saw_start_tl_trans = 1'b1;
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
        // Status register
        exp_read_data = '{upd: 1'b1, chk: 1'b1, val: {31'd0, running}};
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

    // We're only interested in reads. Ignore any acks for memory or register writes that came in on
    // the A channel.
    if (item.is_write())
      return;

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
    end
  endtask

  task process_model_fifo();
    otbn_model_item item;

    forever begin
      model_fifo.get(item);
      `uvm_info(`gfn, $sformatf("received model transaction:\n%0s", item.sprint()), UVM_HIGH)

      case (item.item_type)
        OtbnModelStart: begin
          // We should only see the model start if it was started by a TL transaction on the
          // previous cycle.
          `DV_CHECK_FATAL(waiting_for_model, "model started unbidden!")
          waiting_for_model = 1'b0;
          running = 1'b1;
        end

        OtbnModelDone: begin
          `DV_CHECK_FATAL(running, "Got done signal when we didn't think model was running.")
          running = 1'b0;
        end

        OtbnModelInsn: begin
          // The model agent's monitor should be configured to only emit OtbnModelInsn items if
          // coverage is enabled.
          `DV_CHECK_FATAL(cfg.en_cov)
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

  // We track TL writes that should start the processor and the model transaction that says it has
  // started. There should be a single cycle delay between the two: on the negedge of each clock,
  // convert a "there was a TL write" event (saw_start_tl_trans) to "we expect to see the model
  // start" (waiting_for_model).
  //
  // If we get to a negedge where waiting_for_model is true, that means that the model didn't start
  // when we expected it to.
  task check_start();
    forever begin
      @(cfg.clk_rst_vif.cbn);

      if (!cfg.clk_rst_vif.rst_n) begin
        // We're in reset. Wait until we start again.
        @(posedge cfg.clk_rst_vif.rst_n);
      end else begin
        // We're not in reset. Check that waiting_for_model is false. If not, we've had a cycle
        // since the model should have started.
        `DV_CHECK(!waiting_for_model, "model didn't start when we expected it to")

        // If we've just seen a write to the CMD register that should start OTBN, set the
        // waiting_for_model flag. This gives a single cycle delay (on the next cycle, we'll check
        // it worked properly using the DV_CHECK above).
        if (saw_start_tl_trans) begin
          waiting_for_model = 1'b1;
          saw_start_tl_trans = 1'b0;
        end
      end
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

endclass
