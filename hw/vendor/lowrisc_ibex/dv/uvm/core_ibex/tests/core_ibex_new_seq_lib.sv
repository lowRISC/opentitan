// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class core_base_new_seq #(type REQ = uvm_sequence_item) extends uvm_sequence #(REQ);

  // Virtual interfaces for driving stimulus directly
  virtual             clk_rst_if   clk_vif;
  virtual core_ibex_dut_probe_if   dut_vif;

  bit                              stop_seq;
  bit                              seq_finished;

  rand bit                         zero_delays;
  // CONTROL_KNOB: Randomly override the delay between stimulus items to be zero
  // Default set to 50% for zero delay to be picked. Set to 100 if zero delay is required always.
  int unsigned                     zero_delay_pct = 50;
  constraint zero_delays_c {
     zero_delays dist {1 :/ zero_delay_pct,
                       0 :/ 100 - zero_delay_pct};
  }

  rand int unsigned                 stimulus_delay_cycles;
  // CONTROL_KNOB: Delay the start of each stimulus a randomized amount (transaction to transaction delay)
  // Can be randomly overwritten to no delay at all with 'zero_delays'
  int unsigned                      stimulus_delay_cycles_min = 200;
  int unsigned                      stimulus_delay_cycles_max = 400;
  constraint reasonable_delay_c {
     stimulus_delay_cycles inside {[stimulus_delay_cycles_min : stimulus_delay_cycles_max]};
  }

  // CONTROL_KNOB: Set this per-instance to make the stimulus generation repeat : {Once, Multiple, Forever}
  run_type_e iteration_modes = MultipleRuns;

  rand int unsigned                 iteration_cnt;
  // CONTROL_KNOB:  This controls the number of stimulus items generated in a loop for {Multiple} cfg
  int unsigned                      iteration_cnt_max = 20;
  constraint iterations_cnt_c {
     iteration_cnt inside {[1:iteration_cnt_max]};
  }

  `uvm_object_param_utils(core_base_new_seq#(REQ))

  function new (string name = "");
    super.new(name);
    if(!uvm_config_db#(virtual clk_rst_if)::get(null, "", "clk_if", clk_vif)) begin
       `uvm_fatal(`gfn, "Cannot get clk_if")
    end
    if (!uvm_config_db#(virtual core_ibex_dut_probe_if)::get(null, "", "dut_if", dut_vif)) begin
      `uvm_fatal(`gfn, "Cannot get dut_if")
    end
  endfunction

  virtual task pre_body();
    // Randomize once before starting to ensure all unininitialized rand variables have a valid starting value
    this.randomize();
  endtask: pre_body

  virtual task body();
    // core_base_new_seq::body() provides a flexible sequence scheduler, where
    // 'iteration_modes' allows different tests to change the frequency
    // stimulus is generated.

    `uvm_info(`gfn, $sformatf("Running the \"%s\" schedule for stimulus generation",
                              iteration_modes.name()), UVM_LOW)
    stop_seq = 1'b0;
    seq_finished = 1'b0;
    case (iteration_modes)
      SingleRun: begin
        drive_stimulus();
      end
      MultipleRuns: begin
        // We randomize in pre_body(), but double-check we have a valid value here.
        `DV_CHECK_FATAL(iteration_cnt != 0)
        `uvm_info(`gfn, $sformatf("Number of stimulus iterations = %0d", iteration_cnt), UVM_LOW)
        for (int i = 0; i <= iteration_cnt; i++) begin
          `uvm_info(`gfn, $sformatf("Running %0d/%0d", i, iteration_cnt), UVM_LOW)
          drive_stimulus();
        end
      end
      InfiniteRuns: begin
        while (!stop_seq) begin
          drive_stimulus();
        end
        seq_finished = 1'b1;
      end
      default: begin
        `uvm_fatal(`gfn, "Type of run not set")
      end
    endcase
  endtask: body

  task drive_stimulus();
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(zero_delays)
    if(!zero_delays) begin
       // Delay for a randomized amount of cycles
       `DV_CHECK_MEMBER_RANDOMIZE_FATAL(stimulus_delay_cycles)
       `uvm_info(`gfn, $sformatf("stimulus_delay_cycles = %0d", stimulus_delay_cycles), UVM_HIGH)
       clk_vif.wait_clks(stimulus_delay_cycles);
    end
    `uvm_info(get_full_name(), "Starting sequence...", UVM_MEDIUM)
    send_req();
    `uvm_info(get_full_name(), "Exiting sequence", UVM_MEDIUM)
  endtask: drive_stimulus

  // Generate the stimulus with a sequence-specific request
  // Seqs can each implement send_req() differently, such as sending a seq_item,
  // or driving the interface directly.
  virtual task send_req();
    `uvm_fatal(get_full_name(), "This task must be implemented in the extended class")
  endtask

  // Can be called by the sequencer to break out of infinite-loops in body()
  virtual task stop();
    stop_seq = 1'b1;
    `uvm_info(`gfn, "Stopping sequence", UVM_MEDIUM)
    wait (seq_finished == 1'b1);
  endtask

endclass

class irq_new_seq extends core_base_new_seq #(irq_seq_item);

  `uvm_object_utils(irq_new_seq)
  `uvm_object_new

  // Set these 'no_*' bits at the test-level to disable the randomizer from
  // generating each particular type of irq.
  bit no_nmi;
  bit no_fast;
  bit no_external;
  bit no_timer;
  bit no_software;

  int unsigned max_delay = 500;
  int unsigned min_delay = 50;

  rand int interval = min_delay;

  constraint reasonable_interval_c {
    interval inside {[min_delay : max_delay]};
  }

  virtual task send_req();
    irq_seq_item irq;
    irq = irq_seq_item::type_id::create("irq");

    // Raise randomized num of interrupts
    start_item(irq);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(irq,
      // with {"CONSTRAINTS"}
      num_of_interrupt inside {[1:5]};
      no_nmi      -> irq_nm       ==  0;
      no_fast     -> irq_fast     == '0;
      no_external -> irq_external ==  0;
      no_timer    -> irq_timer    ==  0;
      no_software -> irq_software ==  0;)
    finish_item(irq);
    get_response(irq);

    // Delay a randomized amount while interrupts are active
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(interval)
    clk_vif.wait_clks(interval);

    // Drop all interrupts
    start_item(irq);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(irq, num_of_interrupt == 0;)
    finish_item(irq);
    get_response(irq);
  endtask: send_req

endclass: irq_new_seq

// Simple debug sequence
// debug_req is just a single bit sideband signal, use the interface to drive it directly
class debug_new_seq extends core_base_new_seq#(irq_seq_item);

  `uvm_object_utils(debug_new_seq)
  `uvm_object_new

  rand int unsigned pulse_length_cycles;
  int unsigned pulse_length_cycles_min = 75;
  int unsigned pulse_length_cycles_max = 500;

  constraint reasonable_pulse_length_c {
    pulse_length_cycles inside {[pulse_length_cycles_min : pulse_length_cycles_max]};
  }

  virtual task body();
    dut_vif.dut_cb.debug_req <= 1'b0;
    super.body();
  endtask: body

  virtual task send_req();
    `uvm_info(`gfn, "Sending debug request", UVM_HIGH)
    dut_vif.dut_cb.debug_req <= 1'b1;
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(pulse_length_cycles);
    clk_vif.wait_clks(pulse_length_cycles);
    dut_vif.dut_cb.debug_req <= 1'b0;
  endtask

endclass

class memory_error_seq extends core_base_new_seq#(ibex_mem_intf_seq_item);
  core_ibex_vseq               vseq;
  rand bit                     choose_side;
  // When set skip error injection if Ibex is currently handling an exception (incluing IRQs)
  bit                          skip_on_exc = 1'b0;

  error_type_e                 err_type = PickErr;
  rand bit                     inject_intg_err;
  // CONTROL_KNOB: Configure the rate between seeing an integrity error versus seeing a bus error.
  int unsigned                 intg_err_pct = 50;
  constraint inject_intg_err_c {
     inject_intg_err dist {1 :/ intg_err_pct,
                           0 :/ 100 - intg_err_pct};
  }

  `uvm_object_utils(memory_error_seq)
  `uvm_declare_p_sequencer(core_ibex_vseqr)

  function new (string name = "");
    super.new(name);
  endfunction

  virtual task send_req();
    vseq.instr_intf_seq.suppress_error_on_exc = skip_on_exc;
    vseq.data_intf_seq.suppress_error_on_exc  = skip_on_exc;

    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(inject_intg_err)
    // If we expect to see only bus errors, we can enable this assertion. Otherwise
    // integrity errors would cause alerts to trigger.
    `DV_ASSERT_CTRL_REQ("tb_no_alerts_triggered", intg_err_pct == 0)
    case ({err_type, inject_intg_err})
      {IsideErr, 1'b0}: begin
        vseq.instr_intf_seq.inject_error();
      end
      {DsideErr, 1'b0}: begin
        vseq.data_intf_seq.inject_error();
      end
      {PickErr, 1'b0}: begin
        `DV_CHECK_STD_RANDOMIZE_FATAL(choose_side)
        if (choose_side) begin
          vseq.instr_intf_seq.inject_error();
        end else begin
          vseq.data_intf_seq.inject_error();
        end
      end
      {IsideErr, 1'b1}: begin
        vseq.instr_intf_seq.inject_intg_error();
      end
      {DsideErr, 1'b1}: begin
        vseq.data_intf_seq.inject_intg_error();
      end
      {PickErr, 1'b1}: begin
        `DV_CHECK_STD_RANDOMIZE_FATAL(choose_side)
        if (choose_side) begin
          vseq.instr_intf_seq.inject_intg_error();
        end else begin
          vseq.data_intf_seq.inject_intg_error();
        end
      end
      default: begin
        // DO nothing
      end
    endcase
  endtask

endclass: memory_error_seq

class fetch_enable_seq extends core_base_new_seq#(irq_seq_item);

  `uvm_object_utils(fetch_enable_seq)
  `uvm_object_new

  int unsigned max_delay = 500;
  int unsigned min_delay = 1;
  bit all_off_values = 0;

  virtual task body();
    // SecureIbex configurations use a MUBI value for fetch enable so there are multiple off values,
    // all should be tested. For other configurations only the bottom bit of the signal is used so
    // there is a single off value
    if (!uvm_config_db#(bit)::get(null, "", "SecureIbex", all_off_values)) begin
      all_off_values = 0;
    end

    dut_vif.dut_cb.fetch_enable <= ibex_pkg::IbexMuBiOn;
    super.body();
  endtask: body

  virtual task send_req();
    ibex_pkg::ibex_mubi_t fetch_enable_off;
    int unsigned          off_delay;

    if (all_off_values) begin
      // Randomise the MUBI fetch_enable value to be one of the many possible off values
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(fetch_enable_off,
        fetch_enable_off != ibex_pkg::IbexMuBiOn;)
    end else begin
      // Otherwise use single fixed off value
      fetch_enable_off = ibex_pkg::IbexMuBiOff;
    end

    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(off_delay,
      off_delay inside {[min_delay : max_delay]};)

    dut_vif.dut_cb.fetch_enable <= fetch_enable_off;
    clk_vif.wait_clks(off_delay);
    dut_vif.dut_cb.fetch_enable <= ibex_pkg::IbexMuBiOn;

  endtask

endclass
