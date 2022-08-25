// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//
// Base class for all OTBN test sequences
//

class otbn_base_vseq extends cip_base_vseq #(
  .CFG_T              (otbn_env_cfg),
  .RAL_T              (otbn_reg_block),
  .COV_T              (otbn_env_cov),
  .VIRTUAL_SEQUENCER_T(otbn_virtual_sequencer)
);
  `uvm_object_utils(otbn_base_vseq)
  `uvm_object_new

  // "Running" flag to detect concurrent executions of run_otbn()
  protected bit running_ = 1'b0;

  // The longest run seen in calls to start_running_otbn. This gets reset to zero by load_elf (since
  // we assume we've got a new program, which might take a different amount of time)
  protected int unsigned longest_run_ = 0;

  // This flag is set in the common vseq to re-enable the checks done by check_no_fatal_alerts
  protected bit enable_base_alert_checks = 1'b0;

  // This flag is configured at the start of _run_sideload_sequence() when it decides whether a run
  // should allow an absent key (in which case, we have to disable end-address checking).
  protected bit absent_key_allowed = 1'b0;

  // This counter is set in run_otbn() if our operation has finished and we're trying to stop. It's
  // used by the code in _run_sideload_sequence() to spot that we should stop sending sideload keys
  // and that it should exit. (Note that we can't just use something like 'disable fork' because the
  // sideload sequencer will get upset if we kill a process that's waiting for a grant from it).
  protected int unsigned stop_tokens = 0;

  // Saved TL agent configuration
  typedef struct packed {
    bit          valid;
    int unsigned a_valid_delay_min;
    int unsigned a_valid_delay_max;
    int unsigned d_ready_delay_min;
    int unsigned d_ready_delay_max;
  } saved_tl_cfg_t;
  protected saved_tl_cfg_t saved_tl_cfg;

  // Overridden from dv_base_vseq
  task dut_init(string reset_kind = "HARD");
    // Always drive the lifecycle escalation signal to off at the start of the sequence.
    cfg.escalate_vif.reset_signals();

    super.dut_init(reset_kind);
  endtask

  // Load the contents of an ELF file into the DUT's memories, either by a DPI backdoor (if backdoor
  // is true) or with TL transactions. Also, pass loop warp rules to the ISS through the model.
  protected task load_elf(string path, bit backdoor);
    otbn_pkg::cmd_e wipe_cmd;
    bit [1:0] num_wipes;
    bit bogus_write;
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(
    bogus_write,
    bogus_write dist {
      0 :/ 1,
      1 :/ 9
    };)
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(num_wipes, num_wipes inside {[0 : 2]};)
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(wipe_cmd, wipe_cmd != otbn_pkg::CmdExecute;)
    if (bogus_write) begin
      // Write a bogus value while we are in IDLE state for coverage.
      _send_bogus_cmd();
    end
    case (num_wipes)
      1: _run_otbn_cmd(wipe_cmd);  // Run a random wipe command
      2: begin
        // First run a random wipe command
        _run_otbn_cmd(wipe_cmd);
        // We also would like to try writing to register while we are not in IDLE.
        // In order to do tht we need to insert a random delay between the operations.
        // That would result with us sometimes successfully running back to back operations.
        // And sometimes writing to CMD while still doing the first operation.
        repeat ($urandom_range(0, 20)) @(cfg.clk_rst_vif.cbn);
        // Check the name of the first command, run the other one after the delay.
        if (wipe_cmd.name() == "CmdSecWipeDmem") _run_otbn_cmd(otbn_pkg::CmdSecWipeImem);
        else _run_otbn_cmd(otbn_pkg::CmdSecWipeDmem);
      end
      default: ;  // Do nothing
    endcase
    if (backdoor) begin
      load_elf_backdoor(path);
    end else begin
      load_elf_over_bus(path);
    end

    // Pass loop warp rules that we've just loaded into otbn_memutil into the model.
    cfg.model_agent_cfg.vif.take_loop_warps(cfg.mem_util);

    if (cfg.model_agent_cfg.vif.has_loop_warps(cfg.mem_util)) begin
      // Where loop warps are present an assertion within prim_count must be disabled.
      cfg.loop_vif.control_loop_counters_out_set_assertion(1'b0);
    end else begin
      // Otherwise enable the assertions as they may have been disabled by a prior elf execution.
      cfg.loop_vif.control_loop_counters_out_set_assertion(1'b1);
    end

    // We're loading a new program, so the tracking that we've been doing for how long runs take is
    // no longer valid.
    longest_run_ = 0;
  endtask

  // Load the contents of an ELF file into the DUT's memories by a DPI backdoor
  protected function void load_elf_backdoor(string path);
    if (!OtbnMemUtilLoadElf(cfg.mem_util, path)) begin
      `uvm_fatal(`gfn, $sformatf("Failed to load ELF at `%0s'", path))
    end
  endfunction

  protected function void save_tl_config();
    `DV_CHECK_FATAL(!saved_tl_cfg.valid)
    saved_tl_cfg.a_valid_delay_min = cfg.m_tl_agent_cfg.a_valid_delay_min;
    saved_tl_cfg.a_valid_delay_max = cfg.m_tl_agent_cfg.a_valid_delay_max;
    saved_tl_cfg.d_ready_delay_min = cfg.m_tl_agent_cfg.d_ready_delay_min;
    saved_tl_cfg.d_ready_delay_max = cfg.m_tl_agent_cfg.d_ready_delay_max;
    saved_tl_cfg.valid = 1'b1;
  endfunction

  protected function void restore_tl_config();
    `DV_CHECK_FATAL(saved_tl_cfg.valid)
    cfg.m_tl_agent_cfg.a_valid_delay_min = saved_tl_cfg.a_valid_delay_min;
    cfg.m_tl_agent_cfg.a_valid_delay_max = saved_tl_cfg.a_valid_delay_max;
    cfg.m_tl_agent_cfg.d_ready_delay_min = saved_tl_cfg.d_ready_delay_min;
    cfg.m_tl_agent_cfg.d_ready_delay_max = saved_tl_cfg.d_ready_delay_max;
    saved_tl_cfg.valid = 1'b0;
  endfunction

  protected function void speed_up_tl_config();
    cfg.m_tl_agent_cfg.a_valid_delay_min = 0;
    cfg.m_tl_agent_cfg.a_valid_delay_max = 0;
    cfg.m_tl_agent_cfg.d_ready_delay_min = 0;
    cfg.m_tl_agent_cfg.d_ready_delay_max = 0;
  endfunction

  // Load the contents of an ELF file into the DUT's memories by TL transactions
  protected task load_elf_over_bus(string path);
    otbn_loaded_word        to_load         [$];
    bit              [33:0] opns            [$];
    bit                     run_fast;
    semaphore               tx_sem = new(0);

    // First, tell OtbnMemUtil to stage the ELF. This reads the file and stashes away the segments
    // we need. If something goes wrong, it will print a message to stderr, so we can just fail.
    if (!OtbnMemUtilStageElf(cfg.mem_util, path)) begin
      `uvm_fatal(`gfn, $sformatf("Failed to stage ELF at `%0s'", path))
    end

    // Next, we need to get the data to be loaded across the "DPI barrier" and into SystemVerilog.
    // We make a queue of the things that need loading (in address order). We'll index into that
    // queue in the "operations" list below.
    get_queue_entries(1'b0, to_load);
    get_queue_entries(1'b1, to_load);

    // Temporarily configure the TL agent to run much quicker 90% of the time. There's no real
    // benefit to testing randomised delays here: we're just writing to a bunch of memory addresses!
    save_tl_config();
    run_fast = $urandom_range(0, 99) < 90;
    if (run_fast) begin
      `uvm_info(`gfn, "Using high-speed TL config for front-door ELF load", UVM_HIGH)
      speed_up_tl_config();
    end

    // The operations that we might perform are:
    //
    //  - Write a word from to_load into IMEM or DMEM
    //  - Set LOAD_CHECKSUM to some value
    //  - Read LOAD_CHECKSUM (the scoreboard will check the result)
    //
    // Represent these operations as a pair {op, value} where op is 0, 1 or 2 for the operations
    // above and value is a 32-bit value that gives an index into to_load if op is zero, a random
    // value to write to LOAD_CHECKSUM if op is one, and is ignored if op is two.
    //
    // We just write to LOAD_CHECKSUM a couple of times (since writing it too often might actually
    // hide a bug). We read from LOAD_CHECKSUM roughly once every 10 writes.
    //
    // In "fast mode", we don't do the parallel LOAD_CHECKSUM reads and writes. Running non-blocking
    // means that UVM sees pending accesses from the register overlapping with calls to predict()
    // that update it for memory writes. I'm not sure what is the proper way to handle this, but I
    // don't think it's possible to do with the current OT base classes.
    foreach (to_load[i]) opns.push_back({2'b00, 32'(i)});
    if (!run_fast) begin
      for (int i = 0; i < 2; ++i) begin
        bit [31:0] value;
        `DV_CHECK_STD_RANDOMIZE_FATAL(value)
        opns.push_back({2'b01, value});
      end
      for (int i = 0; i < to_load.size() / 10; ++i) opns.push_back({2'b10, 32'd0});
    end

    // Shuffle opns so that we perform them in an arbitrary order
    opns.shuffle();

    // Send the writes, one by one. We want to run in non-blocking mode to avoid each write waiting
    // for its predecessor. But we also need to be certain that all of the writes have actually
    // happened. To make this work, we run the CSR operations in blocking mode and do the "fork /
    // join_none" here instead. That way, we can decrement a counter to see when stuff is done.
    foreach (opns[i]) begin
      automatic bit [ 1:0] op;
      automatic bit [31:0] value;
      {op, value} = opns[i];

      if (run_fast) begin
        // Non-blocking mode
        fork
          begin
            send_mem_operation(to_load, op, value);
            tx_sem.put();
          end
        join_none
      end else begin
        // Blocking mode
        send_mem_operation(to_load, op, value);
        tx_sem.put();
      end
    end

    // Block until each of the operations above has done a 'put'
    tx_sem.get(opns.size());

    // Do a final read of LOAD_CHECKSUM. If we are in 'fast mode', this is the only one we'll do.
    begin
      uvm_reg_data_t reg_val;
      csr_utils_pkg::csr_rd(ral.load_checksum, reg_val);
    end

    restore_tl_config();
  endtask

  protected task send_mem_operation(otbn_loaded_word to_load[$], bit [1:0] op, bit [31:0] value);
    case (op)
      2'b00:
      csr_utils_pkg::mem_wr(to_load[value].for_imem ? ral.imem : ral.dmem, to_load[value].offset,
                            to_load[value].data);
      2'b01: csr_utils_pkg::csr_wr(ral.load_checksum, value);
      2'b10: begin
        uvm_reg_data_t reg_val;
        csr_utils_pkg::csr_rd(ral.load_checksum, reg_val);
      end
      default: `uvm_fatal(`gfn, "Invalid operation")
    endcase
  endtask

  protected function automatic void get_queue_entries(bit for_imem,
                                                      ref otbn_loaded_word entries[$]);
    // Get the bus-accessible size of this memory (to make sure the number of loaded words makes
    // sense)
    int unsigned mem_size = for_imem ? OTBN_IMEM_SIZE : OTBN_DMEM_SIZE;

    // Iterate over the segments for this memory
    int seg_count = OtbnMemUtilGetSegCount(cfg.mem_util, for_imem);
    for (int seg_idx = 0; seg_idx < seg_count; seg_idx++) begin

      // What offset and size (in 32 bit words) is this segment?
      bit [31:0] seg_off, seg_size;
      if (!OtbnMemUtilGetSegInfo(cfg.mem_util, for_imem, seg_idx, seg_off, seg_size)) begin
        `uvm_fatal(`gfn, $sformatf("Failed to get segment info for segment %0d.", seg_idx))
      end

      // Add each word.
      for (bit [31:0] i = 0; i < seg_size; i++) begin
        bit [31:0] word_off, data;
        otbn_loaded_word entry;

        word_off = seg_off + i;

        if (!OtbnMemUtilGetSegData(cfg.mem_util, for_imem, word_off, data)) begin
          `uvm_fatal(`gfn, $sformatf("Failed to get segment data at word offset %0d.", word_off))
        end

        // Since we know that the segment data lies in IMEM or DMEM and that this fits in the
        // address space, we know that the top two bits of the word address are zero.
        `DV_CHECK_FATAL(word_off[31:30] == 2'b00)

        // OtbnMemUtil should have checked that this address was valid for the given memory, but it
        // can't hurt to check again.
        `DV_CHECK_FATAL({word_off, 2'b00} < {2'b00, mem_size})

        entry.for_imem = for_imem;
        entry.offset   = word_off[21:0];
        entry.data     = data;
        entries.push_back(entry);
      end
    end
  endfunction

  // Write a random CMD value, which may or may not be a valid command.
  //
  // This is only used when OTBN is either known to be locked or running (so it will ignore the
  // write) or is known to be ready to receive a command (For example, maybe we tried to send the
  // command when it was running, but were a little bit late. That would still be fine because we
  // know that we've got an ELF file loaded up)
  //
  // Note that the CMD register just contains an 8-bit field. We randomise the top bits here, but
  // they should have no effect.
  protected task _send_random_cmd();
    logic [31:0] val;
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(val,
                                       val[7:0] dist {
                                         otbn_pkg::CmdExecute     :/ 2,
                                         otbn_pkg::CmdSecWipeDmem :/ 2,
                                         otbn_pkg::CmdSecWipeImem :/ 2,
                                         [0 : $]                  :/ 1
                                       };)
    `uvm_info(`gfn, $sformatf("\n\t ----| Writing a random value (0x%08h) to CMD register", val),
              UVM_MEDIUM)
    csr_utils_pkg::csr_wr(ral.cmd, val);
  endtask

  // Write a bogus CMD value, which is definitely not a valid command
  protected task _send_bogus_cmd();
    logic [31:0] val;
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(val,
                                       !(val[7:0] inside {otbn_pkg::CmdExecute,
                                                          otbn_pkg::CmdSecWipeDmem,
                                                          otbn_pkg::CmdSecWipeImem});)
    `uvm_info(`gfn, $sformatf("\n\t ----| Writing a bogus value (0x%08h) to CMD register", val),
              UVM_MEDIUM)
    csr_utils_pkg::csr_wr(ral.cmd, val);
  endtask

  // Start OTBN and then wait until done
  //
  // If the block gets reset, this task will exit early.
  protected task run_otbn(input check_end_addr = 1);
    int exp_end_addr;
    int rd_pc;
    int wr_pc;

    // Check that we haven't been called re-entrantly. This could happen if there's a bug in the
    // reset sequence, which relies on run_otbn() to exit properly when it sees a device reset.
    // Explode here if that happens, which should be easier to debug than two concurrent run_otbn()
    // processes fighting over the interface.
    `DV_CHECK_FATAL(!running_)
    `DV_CHECK_FATAL(stop_tokens == 0)
    running_ = 1'b1;

    // Check that we aren't currently in reset. If we were, this task would otherwise exit
    // immediately, causing all sorts of confusion. It's a testbench bug if we are.
    `DV_CHECK_FATAL(!cfg.under_reset)

    // Wait for OTBN to be idle. After a reset, getting an URND value from EDN and performing an
    // initial secure wipe can take up to 500 cycles if the EDN is held in reset for much longer
    // than OTBN, so use that as timeout.  Stop waiting on a reset.
    fork : wait_for_idle_fork
      wait(cfg.model_agent_cfg.vif.status == otbn_pkg::StatusIdle);
      repeat (500) @(cfg.clk_rst_vif.cbn);
      wait(cfg.under_reset);
    join_any

    // Exit early if:
    // - OTBN has been reset during the initial secure wipe; or
    // - OTBN went from the initial secure wipe directly into the Locked state due to a fatal
    //   internal error (e.g., on URND).
    if (cfg.under_reset || cfg.model_agent_cfg.vif.status == otbn_pkg::StatusLocked) begin
      running_ = 1'b0;
      return;
    end

    `DV_CHECK_FATAL(cfg.model_agent_cfg.vif.status == otbn_pkg::StatusIdle,
                    "Timed out waiting for OTBN to be idle before execution");

    fork : isolation_fork
      begin
        fork
          // Only _run_otbn_cmd will complete
          _run_otbn_cmd(otbn_pkg::CmdExecute);
          _run_loop_warps();
          _run_sideload_sequence();
          _run_rnd_edn_rsp();
        join_any

        // Consumed by _run_sideload_sequence()
        stop_tokens = 1;

        wait(!stop_tokens);

        // Kill any processes that didn't use the stop token mechanism
        disable fork;
      end
    join

    // The wait for OTBN to finish short-circuits and exits immediately if the reset line goes low.
    // If that happens, we don't want to run any further checks (since the run didn't finish
    // properly).
    if (cfg.under_reset) begin
      running_ = 1'b0;
      return;
    end

    // Post-run checks ///////

    // Disable the end-address check if the sideload key is allowed to be absent, because that might
    // mean a read from the key sideload WSR will fail unpredictably.
    if (check_end_addr && !absent_key_allowed) begin
      // If there was an expected end address, compare it with the model. This isn't really a test of
      // the RTL, but it's handy to make sure that the RIG really is generating the control flow that
      // it expects.
      exp_end_addr = OtbnMemUtilGetExpEndAddr(cfg.mem_util);
      if (exp_end_addr >= 0) begin
        `DV_CHECK_EQ_FATAL(exp_end_addr, cfg.model_agent_cfg.vif.stop_pc)
      end
    end

    // If OTBN stopped with an error then it should trigger a recoverable or fatal alert. The
    // scoreboard is already checking that this goes out properly, but we don't want to follow up
    // with another execution before that happens. The problem is that the alert system sometimes
    // takes a while to actually send the alert and the second operation might also generate an
    // alert in the meantime, causing great confusion!
    //
    // It's a bit awkward to track whether there's a pending alert (because in the worst case, it
    // might have gone out before the status change at the end of the operation) and we're already
    // handling that logic in the scoreboard, so we can just wait here until the scoreboard's "I'm
    // waiting for an alert" flags have been cleared. If this was a recoverable alert, we then wait
    // until the handshake is done (because we can't send a new alert until that finishes).
    while (cfg.scoreboard.fatal_alert_expected || cfg.scoreboard.recov_alert_expected) begin
      @(posedge cfg.clk_rst_vif.clk or negedge cfg.clk_rst_vif.rst_n);
      if (!cfg.clk_rst_vif.rst_n) break;
    end
    cfg.m_alert_agent_cfg["recov"].vif.wait_ack_complete();

    if (cfg.model_agent_cfg.vif.status == otbn_pkg::StatusLocked) begin
      bit cmd_wr;
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(
      cmd_wr,
      cmd_wr dist {
        0 :/ 9,
        1 :/ 1
      };)
      if (cmd_wr) begin
        `uvm_info(`gfn, "entered locked status. Writing to cmd register", UVM_LOW)
        _send_random_cmd();
      end
    end

    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(rd_pc, rd_pc inside {[0 : 100]};)
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(wr_pc, wr_pc inside {[0 : 100]};)
    if (rd_pc <= 50) begin
      uvm_reg_data_t reg_val;
      csr_utils_pkg::csr_rd(ral.err_bits, reg_val);
    end
    if (wr_pc <= 25) begin
      bit [31:0] wdata;
      `DV_CHECK_STD_RANDOMIZE_FATAL(wdata)
      csr_utils_pkg::csr_wr(ral.err_bits, wdata);
    end

    // Note: This must be the last thing in the function before we return. We use this flag to
    // synchronise with a "disable fork" in start_running_otbn().
    running_ = 1'b0;
  endtask

  // The guts of the run_otbn task. Writes to the CMD register to start OTBN and polls the status
  // register until completion. On reset, this returns immediately.
  protected task _run_otbn_cmd(logic [7:0] cmd_i);

    logic [7:0] exp_data_status;
    case (cmd_i)
      otbn_pkg::CmdSecWipeDmem: begin
        `uvm_info(`gfn, "\n\t ----| Starting OTBN SecWipeDmem", UVM_MEDIUM)
        exp_data_status = otbn_pkg::StatusBusySecWipeDmem;
      end
      otbn_pkg::CmdSecWipeImem: begin
        `uvm_info(`gfn, "\n\t ----| Starting OTBN SecWipeImem", UVM_MEDIUM)
        exp_data_status = otbn_pkg::StatusBusySecWipeImem;
      end
      otbn_pkg::CmdExecute: begin
        `uvm_info(`gfn, "\n\t ----| Starting OTBN Execution", UVM_MEDIUM)
        exp_data_status = otbn_pkg::StatusBusyExecute;
      end
      default: `uvm_fatal(`gfn, "Invalid operation")
    endcase

    csr_utils_pkg::csr_wr(ral.cmd, cmd_i);

    // Wait for OTBN to finish, either by polling or by waiting on the interrupt pins
    if (_pick_use_interrupt()) begin
      `uvm_info(`gfn, "\n\t ----| Waiting for OTBN to finish (interrupt)", UVM_MEDIUM)
      wait_for_interrupt();
    end else begin
      `uvm_info(`gfn, "\n\t ----| Waiting for OTBN to finish (polling)", UVM_MEDIUM)
      csr_utils_pkg::csr_spinwait(.ptr(ral.status), .exp_data(exp_data_status),
                                  .compare_op(CompareOpNe));
    end

    if (cfg.clk_rst_vif.rst_n) begin
      if (exp_data_status == otbn_pkg::StatusBusyExecute) begin
        `uvm_info(`gfn, "\n\t ----| OTBN completed execution", UVM_MEDIUM)
        // After execution, OTBN securely wipes its internal state, so wait until that is complete.
        exp_data_status = otbn_pkg::StatusBusySecWipeInt;
        csr_utils_pkg::csr_spinwait(.ptr(ral.status), .exp_data(exp_data_status),
                                    .compare_op(CompareOpNe));
        `uvm_info(`gfn, "\n\t ----| OTBN completed secure wipe", UVM_MEDIUM)
      end else begin
        `uvm_info(`gfn, "\n\t ----| OTBN finished", UVM_MEDIUM)
      end
    end else begin
      `uvm_info(`gfn, "\n\t ----| OTBN reset", UVM_MEDIUM)
    end
  endtask

  // How should we wait until OTBN has finished?
  //
  // Use polling if OTBN is not idle, the interrupt is disabled or if the interrupt pin is already
  // high. If enabled, wait on the interrupt pin except occasionally (poll_despite_interrupts_pct).
  // This exceptional case is to spot any weirdness in updating the STATUS register when interrupts
  // are enabled.
  protected function bit _pick_use_interrupt();
    uvm_status_e   peek_status;
    uvm_reg_data_t peek_value;

    // If OTBN is not in the IDLE state, starting an operation won't actually do anything, and we
    // won't get a follow-up interrupt. So we shouldn't wait for an interrupt in this case!
    if (cfg.model_agent_cfg.vif.status != otbn_pkg::StatusIdle) begin
      return 1'b0;
    end

    // We can just use the RAL prediction for the enable register (since it's only updated by TL
    // accesses).
    if (ral.intr_enable.done.get() == 0) begin
      return 1'b0;
    end

    // The interrupt is enabled, but maybe its state is already high. In that case, we can't use it
    // to spot whether we've finished.
    if (cfg.intr_vif.pins[0]) begin
      return 1'b0;
    end

    // The interrupt is enabled and not currently triggered. Use the interrupt except
    // poll_despite_interrupts_pct percent of the time.
    return $urandom_range(100) > cfg.poll_despite_interrupts_pct;
  endfunction

  // Poll RND EDN request to set some constrained randomness as a response from EDN agent.
  virtual task _run_rnd_edn_rsp();
    forever begin
      @(negedge cfg.clk_rst_vif.clk);
      if (cfg.poll_rnd_edn_req()) cfg.gen_rnd_edn_rsp();
    end
  endtask

  // Monitor the bound-in loop controller interface to take action on loop warp events. Runs
  // forever, but is spawned by run_otbn(), which will kill it when the OTBN run completes or the
  // block is reset.
  protected task _run_loop_warps();
    logic [31:0] addr, old_iters, old_count;
    bit [31:0] new_count, new_iters;
    bit [31:0] loop_stack_rd_idx;

    forever begin
      // Run on the negative edge of the clock: we want to force a "_d" value, so should make sure
      // we get in after the DUT's logic that runs on posedge.
      @(negedge cfg.clk_rst_vif.clk);

      // If the loop stack is empty (so we don't have a current loop), there's nothing to do here.
      if (cfg.loop_vif.get_fullness() == StackEmpty) continue;

      // Get the current address and iteration counter.
      addr = cfg.loop_vif.insn_addr_i;
      old_iters = cfg.loop_vif.current_loop_q_iterations;

      // Convert from the "RTL view" of the iteration count (counting down to 1) to the "ISA view"
      // (counting up from zero).
      old_count = cfg.loop_vif.loop_iters_to_count(old_iters);

      // Do a DPI call to otbn_memutil to look up whether there is a loop warp that we should be
      // taking. This returns 1'b1 and fills in new_count if there is a warp that does something.
      if (!OtbnMemUtilGetLoopWarp(cfg.mem_util, addr, old_count, new_count)) continue;

      // Loop warping assumes we're not manipulating the loop stack (i.e. no new loop starting or
      // current loop finishing the same cycle we warp).
      `DV_CHECK_FATAL(!(cfg.loop_vif.loop_stack_push || cfg.loop_vif.loop_stack_pop))

      // Convert loop warp's remaining iteration count to "RTL view"
      new_iters = cfg.loop_vif.loop_count_to_iters(new_count);

      _set_loop_counter(cfg.loop_vif.loop_stack_rd_idx, new_iters);
    end
  endtask

  // Set a counter in the loop stack to a specified value
  protected function void _set_loop_counter(bit [31:0] loop_counter_idx, bit [31:0] new_count);
    bit [1:0][31:0] new_cnt_q;
    bit [1:0][31:0] new_cnt_d;
    string counter_path, index;
    string deposit_path_d, deposit_path_q;

    counter_path = $sformatf("u_otbn_loop_controller.g_loop_counters[%0d].u_loop_count",
                             cfg.loop_vif.loop_stack_rd_idx);

    // The prim_count primitive employs a "cross" counter, meaning that it contains a set of two
    // counters where the secondary counter counts in reverse direction. Both counters have to sum
    // up to 2**Width-1 = 2**32-1 = 32'hFFFF_FFFF at all times. The primitive can both increment
    // and decrement the primary counter and in this particular case, this primary counter counts
    // the remaining loop iterations. Whenever we force the primary counter to "new_count", we also
    // have to calculate and set the value of the secondary counter to the inverse, accordingly.
    new_cnt_q[0] = new_count;
    new_cnt_q[1] = 32'hFFFF_FFFF - new_count;
    if (cfg.loop_vif.current_loop_q_iterations != cfg.loop_vif.current_loop_d_iterations) begin
      // The primary counter counts down in this case, and the secondary counter counts up.
      `DV_CHECK_EQ_FATAL(cfg.loop_vif.current_loop_q_iterations - 1,
                         cfg.loop_vif.current_loop_d_iterations)
      new_cnt_d[0] = new_cnt_q[0] - 1;
      new_cnt_d[1] = new_cnt_q[1] + 1;
    end else begin
      // No iteration count change so _d == _q
      new_cnt_d = new_cnt_q;
    end

    for (int k = 0; k < 2; k++) begin
      index = $sformatf("[%0d]", k);
      deposit_path_d =
          $sformatf({"tb.dut.u_otbn_core.u_otbn_controller.", counter_path, ".cnt_d", index});
      deposit_path_q =
          $sformatf({"tb.dut.u_otbn_core.u_otbn_controller.", counter_path, ".cnt_q", index});

      `DV_CHECK_FATAL(uvm_hdl_deposit(deposit_path_d, new_cnt_d[k]) == 1, {
                      "Failed to override cnt_d", index, " for loop warp."})

      `DV_CHECK_FATAL(uvm_hdl_deposit(deposit_path_q, new_cnt_q[k]) == 1, {
                      "Failed to override cnt_q", index, " for loop warp."})
    end
  endfunction

  // Run the correct key sideload sequence
  protected task _run_sideload_sequence();
    // First, pick a value for absent_key_allowed. This will be used here to configure the sideload
    // sequence and then will be checked at the end of run_otbn().
    absent_key_allowed = $urandom_range(100) <= cfg.allow_no_sideload_key_pct;

    if (absent_key_allowed) begin
      // If absent keys are allowed, the default sideload sequence (which should be running already)
      // will work just fine. Wait until we're told to stop and then exit.
      wait(stop_tokens != 0);
    end else begin
      // If absent keys are not allowed, we want to generate our own sequence that doesn't allow
      // keys to be invalid. We send it with a higher priority to override the default sequence.
      key_sideload_set_seq #(keymgr_pkg::otbn_key_req_t) sideload_seq;
      `uvm_create_on(sideload_seq, p_sequencer.key_sideload_sequencer_h)
      while (stop_tokens == 0) begin
        `DV_CHECK_RANDOMIZE_WITH_FATAL(sideload_seq, sideload_key.valid == 1'b1;)
        `uvm_send_pri(sideload_seq, 200)
      end
    end

    `DV_CHECK_FATAL(stop_tokens > 0);
    stop_tokens -= 1;
  endtask

  virtual protected function string pick_elf_path();
    chandle helper;
    int     num_files;
    string  elf_path;

    // Check that cfg.otbn_elf_dir was set by the test
    `DV_CHECK_FATAL(cfg.otbn_elf_dir.len() > 0);

    // Pick an ELF file to use in the test. We have to do this via DPI (because you can't list a
    // directory in pure SystemVerilog). To do so, we have to construct a helper object, which will
    // look after memory allocation for the string holding the path.
    helper = OtbnTestHelperMake(cfg.otbn_elf_dir);
    `DV_CHECK_FATAL(helper != null)

    // Ask the helper how many files there are. If it returns zero, the directory name is bogus or
    // the directory is empty.
    num_files = OtbnTestHelperCountFilesInDir(helper);
    `DV_CHECK_FATAL(num_files > 0, $sformatf(
                    "No regular files found in directory `%0s'.", cfg.otbn_elf_dir))

    // Pick a file, any file... Note that we pick an index on the SV side so that we use the right
    // random seed. Then we convert back to a filename with another DPI call. If the result is the
    // empty string, something went wrong.
    elf_path = OtbnTestHelperGetFilePath(helper, $urandom_range(num_files - 1));
    `DV_CHECK_FATAL(elf_path.len() > 0, "Bad index for ELF file")

    // Use sformat in a trivial way to take a copy of the string, so we can safely free helper (and
    // hence the old elf_path) afterwards.
    elf_path = $sformatf("%0s", elf_path);

    // Now that we've taken a copy of elf_path, we can safely free the test helper.
    OtbnTestHelperFree(helper);

    return elf_path;
  endfunction

  // Start running OTBN (forking off a run_otbn task) and return when it's still going.
  //
  // This works by guessing the number of cycles to run and then returning after that time. Of
  // course, the run_otbn task might actually finish in less time than that! If so, we run a second
  // time and guess a smaller value.
  //
  // This can be used to implement things like the reset test where we want to inject some sort of
  // error part-way into a run.
  task start_running_otbn(bit check_end_addr);
    bit timed_out = 1'b0;

    for (int i = 0; i < 10; i++) begin
      int cycle_counter;
      int unsigned max_wait_cycles;
      int unsigned wait_cycles;

      // Guess the number of cycles until error is injected. The maximum wait is "75% of the longest
      // we've seen the program run before terminating". This should avoid problems where we keep
      // picking times that occur after the program has finished.
      max_wait_cycles = ((longest_run_ > 0) ? longest_run_ : 1000) * 3 / 4;
      wait_cycles = $urandom_range(max_wait_cycles) + 1;
      fork : isolation_fork
        begin
          fork
            run_otbn(.check_end_addr(check_end_addr));
            begin
              wait(cfg.model_agent_cfg.vif.status == otbn_pkg::StatusBusyExecute);
              repeat (wait_cycles) begin
                @(cfg.clk_rst_vif.cbn);
                cycle_counter++;
              end
            end
          join_any

          // When we get here, we know that either the OTBN sequence finished or we timed out
          // and it's still going. We can see whether OTBN is still going by looking at the status
          // from the model (which is also in sync with the RTL). Because we wait on the negedge
          // when updating cycle_counter above, we know we've got the "new version" of the status at
          // this point.
          if (cfg.model_agent_cfg.vif.status inside {otbn_pkg::StatusBusyExecute,
                                                   otbn_pkg::StatusBusySecWipeInt}) begin
            timed_out = 1'b1;
          end else begin
            timed_out = 1'b0;
            // The OTBN sequence finished so update wait_cycles. cycle_counter should be at most equal
            // to wait_cycles because we'll stop at that point. It can be equal if OTBN happens to
            // complete its operation in wait_cycles cycles.
            `DV_CHECK_LE_FATAL(cycle_counter, wait_cycles);
            longest_run_ = cycle_counter;

            // Wait for the run_otbn thread to finish. This will usually be instant, but might take
            // a couple of cycles if we happen to have timed out exactly at the end of the run (when
            // the status has switched, but before run_otbn finishes)
            wait(!running_);

            // Kill the counter thread
            disable fork;
          end
        end
      join
      if (timed_out) break;
    end
    // Insert a random CMD write while we are running for coverage
    _send_random_cmd();
    // If we get here and timed_out is false then something weird has happened: we've run the binary
    // 10 times and each run has taken less than 75% of the time of the previous run. This shouldn't
    // happen!
    `DV_CHECK_FATAL(timed_out, "Failed to pick a working time-out")
  endtask

  // Wait for (the one and only) interrupt to strike. Returns early on reset
  task wait_for_interrupt();
    if (cfg.clk_rst_vif.rst_n && !cfg.intr_vif.pins[0]) begin
      @(negedge cfg.clk_rst_vif.rst_n or posedge cfg.intr_vif.pins[0]);
    end
  endtask

  // Overridden from cip_base_vseq
  //
  // This task in the base sequence checks whether any alerts fire. This doesn't really work for
  // OTBN because it's not in sync with the logic that actually generates the alerts. We handle this
  // properly in the scoreboard so want to disable this check except in otbn_common_vseq (which is
  // used for the generic alert tests).
  task check_no_fatal_alerts();
    if (enable_base_alert_checks) super.check_no_fatal_alerts();
  endtask

  // Task to build a random image in imem
  virtual task imem_init();
    bit   [ 31:0] rnd_data;
    logic [127:0] key;
    logic [ 63:0] nonce;
    bit   [ 38:0] integ_data;

    key   = cfg.get_imem_key();
    nonce = cfg.get_imem_nonce();

    // Randomize the memory contents.
    //
    // We can't just use the mem_bkdr_util randomize_mem function because that doesn't obey the
    // scrambling key. This wouldn't be a problem (the memory is supposed to be random!), except
    // that we also need to pick ECC values that match.
    for (int i = 0; i <= ImemSizeByte / 4; i++) begin
      `DV_CHECK_STD_RANDOMIZE_FATAL(rnd_data)
      integ_data = prim_secded_pkg::prim_secded_inv_39_32_enc(rnd_data);
      cfg.write_imem_word(i, integ_data, key, nonce);
    end
  endtask

  // Task to build a random image in dmem
  virtual task dmem_init();
    bit   [ 31:0] rnd_data;
    logic [127:0] key;
    logic [ 63:0] nonce;
    bit   [ 38:0] integ_data;
    bit   [ 38:0] final_data_arr[8];
    bit   [311:0] final_data;

    key   = cfg.get_dmem_key();
    nonce = cfg.get_dmem_nonce();

    // Randomize the memory contents.
    //
    // We can't just use the mem_bkdr_util randomize_mem function because that doesn't obey the
    // scrambling key. This wouldn't be a problem (the memory is supposed to be random!), except
    // that we also need to pick ECC values that match.
    for (int i = 0; i <= DmemSizeByte / 4; i++) begin
      for (int j = 0; j < 8; j++) begin
        `DV_CHECK_STD_RANDOMIZE_FATAL(rnd_data)
        integ_data = prim_secded_pkg::prim_secded_inv_39_32_enc(rnd_data);
        final_data_arr[j] = integ_data;
      end
      final_data = {>>{final_data_arr}};
      cfg.write_dmem_word(i, final_data, key, nonce);
    end
  endtask

  // Task to check if otbn is in locked state. If otbn is indeed locked, then ensure fatal error is
  // asserted and reset the dut.
  virtual task reset_if_locked();
    uvm_reg_data_t act_val;
    wait (!(cfg.model_agent_cfg.vif.status inside {otbn_pkg::StatusBusyExecute,
                                                   otbn_pkg::StatusBusySecWipeInt}));

    // At this point, our status has changed. We're probably actually seeing the alert now, but make
    // sure that it has gone out in at most 100 cycles.
    if (cfg.model_agent_cfg.vif.status == otbn_pkg::StatusLocked) begin
      fork
        begin
          csr_utils_pkg::csr_rd(.ptr(ral.status), .value(act_val));
          csr_utils_pkg::csr_rd(.ptr(ral.err_bits), .value(act_val));
          csr_utils_pkg::csr_rd(.ptr(ral.fatal_alert_cause), .value(act_val));
        end
        begin
          repeat (3) wait_alert_trigger("fatal", .wait_complete(1));
        end
      join
      do_apply_reset = 1'b1;
      dut_init("HARD");
    end
  endtask
endclass : otbn_base_vseq
