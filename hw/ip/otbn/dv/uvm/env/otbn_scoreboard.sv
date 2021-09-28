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
        // Spot writes to the "cmd" register that tell us to start
        "cmd": begin
          // We start the execution when we see a write of the EXECUTE command. See the comment
          // above pending_start_tl_trans to see how this tracking works.
          if (item.a_data == otbn_pkg::CmdExecute) begin
            // Set a flag: we're expecting the model to start on the next negedge. Also, spawn off a
            // checking thread that will make sure it has been cleared again by the next posedge.
            // Note that the reset() method is only called in the DV base class on the following
            // posedge of rst_n, so we have to check whether we're still in reset here.
            pending_start_tl_trans = 1'b1;
            fork begin
              @(cfg.clk_rst_vif.cb);
              `DV_CHECK_FATAL(!cfg.clk_rst_vif.rst_n || !pending_start_tl_trans,
                              "Model ignored a write of EXECUTE to the CMD register.")
            end
            join_none;
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
    end
  endtask

  task process_model_fifo();
    otbn_model_item item;

    forever begin
      model_fifo.get(item);
      `uvm_info(`gfn, $sformatf("received model transaction:\n%0s", item.sprint()), UVM_HIGH)

      case (item.item_type)
        OtbnModelStatus: begin
          // Has the status changed from idle to busy? If so, we should have seen a write to the
          // command register on the previous posedge. See comment above pending_start_tl_trans for
          // the details.
          if (model_status == otbn_pkg::StatusIdle &&
              item.status inside {otbn_pkg::StatusBusyExecute,
                                  otbn_pkg::StatusBusySecWipeDmem,
                                  otbn_pkg::StatusBusySecWipeImem}) begin
            `DV_CHECK_FATAL(pending_start_tl_trans,
                            "Saw start transaction without corresponding write to CMD")
            pending_start_tl_trans = 1'b0;
          end
          model_status = item.status;
          // If the model status is locked, the scoreboard should expect a fatal error.
          if (model_status == otbn_pkg::StatusLocked) begin
            set_exp_alert("fatal", .is_fatal(1));
          end
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

endclass
