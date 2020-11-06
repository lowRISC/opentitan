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

  // This is incremented on a TL transaction that should start the model and decremented on a model
  // transaction that shows we saw the start signal. In check_start(), we check on every clock edge
  // that it's zero (showing that the TL transaction and model transaction came in on the same
  // cycle, so the two signals are in sync)
  int expect_start_counter = 0;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    model_fifo = new("model_fifo", this);
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    fork
      process_model_fifo();
      check_start();
    join_none
  endtask

  virtual function void reset(string kind = "HARD");
    super.reset(kind);
    // reset local fifos queues and variables
  endfunction

  task process_tl_access(tl_seq_item item, tl_channels_e channel = DataChannel);
    case (channel)
      AddrChannel: process_tl_addr(item);
      DataChannel: process_tl_data(item);
      default: `uvm_fatal(`gfn, $sformatf("Invalid channel: %0h", channel))
    endcase
  endtask

  task process_tl_addr(tl_seq_item item);
    uvm_reg        csr;
    uvm_reg_addr_t csr_addr;
    string         csr_name;

    bit [DataWidth-1:0] dw_one = {{DataWidth-1{1'b0}}, 1'b1};

    // The only TL accesses we currently track are writes to the "start" bit of the CMD register.
    // These start the processor. We don't pass those to the model through UVM, because it's
    // difficult to get the timing right (you only recognise the transaction on the clock edge after
    // you needed to set the signal!), so the testbench actually grabs the model's start signal from
    // the DUT internals. Of course, we need to check this is true exactly when we expect it to be.
    // Here, we set a flag to say that we expect the "start" signal to be high. See the
    // check_start() task, which checks it's true at the right time.
    csr_addr = ral.get_word_aligned_addr(item.a_addr);
    csr = ral.default_map.get_reg_by_offset(csr_addr);

    // csr might be null and that's ok (it's probably a write to memory).
    if (csr == null)
      return;

    // The only TL transactions we're tracking at the moment are writes to the "cmd" register,
    // which tell us to start.
    csr_name = csr.get_name();
    if (csr_name == "cmd") begin

      // We start when we see a write that sets the "start" field of the register. We can read most
      // register fields from the RAL (which is updated by the base scoreboard class), but this
      // register is W1C, so that doesn't really work here.
      if (csr_utils_pkg::get_field_val(cfg.ral.cmd.start, item.a_data)) begin
        this.expect_start_counter++;
      end
    end
  endtask

  task process_tl_data(tl_seq_item item);
    // TODO: Fill this out to do any extra tracking on the data channel
  endtask

  task process_model_fifo();
    otbn_model_item item;
    forever begin
      model_fifo.get(item);
      `uvm_info(`gfn, $sformatf("received model transaction:\n%0s", item.sprint()), UVM_HIGH)

      case (item.item_type)
        OtbnModelStart: begin
          this.expect_start_counter--;
        end
        OtbnModelDone: begin
          // TODO: Handle this signal
        end
        default: `uvm_fatal(`gfn, $sformatf("Bad item type %0d", item.item_type))
      endcase
    end
  endtask

  // After each clock edge (we wait until the next negedge), check that the interface's value of
  // start (which we grabbed out of the design) equals that we'd expect from TL transactions.
  task check_start();
    forever begin
      @(cfg.clk_rst_vif.cbn);
      `DV_CHECK_EQ(this.expect_start_counter, 0)
    end
  endtask

endclass
