// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ibex_icache_core_driver
  extends dv_base_driver #(.ITEM_T     (ibex_icache_core_req_item),
                           .RSP_ITEM_T (ibex_icache_core_rsp_item),
                           .CFG_T      (ibex_icache_core_agent_cfg));
  `uvm_component_utils(ibex_icache_core_driver)
  `uvm_component_new

  // An analysis port that gets hooked up to the scoreboard and the memory agent. This isn't used to
  // report on actual bus traffic (that's done by the monitor, as usual) but is used to report on
  // new memory seeds, which don't in themselves cause any bus traffic.
  uvm_analysis_port #(bit [31:0]) analysis_port;

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    analysis_port = new("analysis_port", this);
  endfunction

  virtual task automatic reset_signals();
    cfg.vif.reset();
  endtask

  // drive trans received from sequencer
  virtual task automatic get_and_drive();
    ibex_icache_core_rsp_item rsp;

    forever begin
      seq_item_port.get_next_item(req);
      `uvm_info(`gfn, $sformatf("rcvd item:\n%0s", req.sprint()), UVM_HIGH)

      rsp = ibex_icache_core_rsp_item::type_id::create("rsp");
      rsp.set_id_info(req);

      rsp.saw_error = 1'b0;

      case (req.trans_type)
        ICacheCoreTransTypeBranch: drive_branch_trans(rsp, req);
        ICacheCoreTransTypeReq:    drive_req_trans(rsp, req);
        default:                   `uvm_fatal(`gfn, "Unknown transaction type")
      endcase

      `uvm_info(`gfn, "item sent", UVM_HIGH)
      seq_item_port.item_done(rsp);
    end
  endtask

  // Drive the cache for a "branch" transaction.
  //
  // This concurrently asserts branch with a given address for a cycle while doing the usual
  // (enable/disable, invalidate, read instructions).
  task automatic drive_branch_trans(ibex_icache_core_rsp_item rsp,
                                    ibex_icache_core_req_item req);
    // Make sure that req is enabled (has no effect unless this is the first transaction)
    cfg.vif.driver_cb.req <= 1'b1;

    // Drive the enable state
    cfg.vif.driver_cb.enable <= req.enable;

    // Maybe drive the ready line high while the branch happens. This should have no effect, but is
    // allowed by the interface so we should make sure it happens occasionally. The signal will be
    // controlled properly by read_insns afterwards.
    cfg.vif.driver_cb.ready <= $urandom_range(16) == 0;

    // Branch, invalidate and set new seed immediately. When the branch has finished, read num_insns
    // instructions until everything is done.
    fork
      begin
        cfg.vif.branch_to(req.branch_addr);
        cfg.vif.driver_cb.ready <= 1'b0;
        fork
          read_insns(rsp, req.num_insns);
        join_any
      end
      if (req.invalidate) invalidate();
      if (req.new_seed != 0) drive_new_seed(req.new_seed);
    join

    disable fork;

  endtask

  // Drive the cache for a "req transaction".
  //
  // This lowers req for zero or more cycles, at the same time as setting the enable pin and (maybe)
  // pulsing the invalidate line. Once that is done, it reads zero or more instructions.
  task automatic drive_req_trans(ibex_icache_core_rsp_item rsp,
                                 ibex_icache_core_req_item req);
    int unsigned req_low_cycles;
    bit          allow_no_low_cycles;

    // How many cycles should we lower the request line? If there aren't any instructions to read,
    // this is constrained to be positive (to avoid a confusing zero-time transaction).
    allow_no_low_cycles = req.num_insns > 0;
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(req_low_cycles,
                                       req_low_cycles dist {
                                           0           :/ (allow_no_low_cycles ? 20 : 0),
                                           [1:33]      :/ 5,
                                           [100:200]   :/ 2,
                                           [1000:1200] :/ 1 };)

    // Drive the enable state
    cfg.vif.driver_cb.enable <= req.enable;

    // Lower req, invalidate and set new seed immediately. After req_low_cycles cycles, start
    // reading instructions (providing there hasn't been a reset).
    fork
      begin
        fork
          if (req_low_cycles > 0) lower_req(req_low_cycles);
          if (req.invalidate) invalidate();
          if (req.new_seed != 0) drive_new_seed(req.new_seed);
        join
        if (cfg.vif.rst_n) read_insns(rsp, req.num_insns);
      end
    join_any

    disable fork;
  endtask

  // Read up to num_insns instructions from the cache, stopping early on an error. If there was an
  // error, fill in the saw_error flag in rsp (which will be passed back to the sequence).
  task automatic read_insns(ibex_icache_core_rsp_item rsp, int num_insns);
    for (int i = 0; i < num_insns; i++) begin
      read_insn();
      // Spot any error and exit early
      if (cfg.vif.driver_cb.err) begin
        rsp.saw_error = 1'b1;
        break;
      end
      // Return early on reset
      if (!cfg.vif.rst_n) break;
    end
  endtask

  // Read a single instruction from the cache
  virtual task automatic read_insn();
    int unsigned delay;

    // Maybe (1 time in 10) wait for a valid signal before even considering asserting ready. Stops
    // early on reset.
    if ($urandom_range(9) == 0) begin
      cfg.vif.wait_valid();
      if (!cfg.vif.rst_n)
        return;
    end

    // Then pick how long we wait before asserting that we are ready.
    //
    // TODO: Make this configurable and weight 0 more heavily.
    cfg.vif.wait_clks($urandom_range(3));

    // Assert ready and then wait until valid. If we see a reset, we stop early
    cfg.vif.driver_cb.ready <= 1'b1;
    while (1'b1) begin
      @(cfg.vif.driver_cb or negedge cfg.vif.rst_n);
      if (cfg.vif.driver_cb.valid || !cfg.vif.rst_n)
        break;
    end

    cfg.vif.driver_cb.ready <= 1'b0;
  endtask

  // Lower the req line for the given number of cycles. Returns early on reset, leaving req low.
  virtual task automatic lower_req(int unsigned num_cycles);
    cfg.vif.driver_cb.req <= 1'b0;
    cfg.vif.wait_clks(num_cycles);
    if (cfg.vif.rst_n) cfg.vif.driver_cb.req <= 1'b1;
  endtask

  // Raise the invalidate line for a randomly chosen number of cycles > 0.
  virtual task automatic invalidate();
    int unsigned num_cycles;
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(num_cycles,
                                       num_cycles dist { 1 :/ 10, [2:20] :/ 1 };)
    cfg.vif.invalidate_pulse(num_cycles);
  endtask

  // If this item specifies a new seed, tell the memory agent and the scoreboard.
  task automatic drive_new_seed(bit [31:0] new_seed);
    `DV_CHECK_FATAL(new_seed != 0);
    analysis_port.write(new_seed);
  endtask

endclass
