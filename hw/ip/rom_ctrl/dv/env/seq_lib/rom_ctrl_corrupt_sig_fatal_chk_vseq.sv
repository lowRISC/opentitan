// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rom_ctrl_corrupt_sig_fatal_chk_vseq extends rom_ctrl_base_vseq;
  `uvm_object_utils(rom_ctrl_corrupt_sig_fatal_chk_vseq)

  `uvm_object_new

  localparam int unsigned RomSizeWords = ROM_SIZE_WORDS;
  localparam int unsigned RomIndexWidth = prim_util_pkg::vbits(RomSizeWords);

  typedef enum bit [3:0] {
      LocalEscalation,
      CheckerCtrConsistency,
      CheckerCtrlFlowConsistency,
      CompareCtrlFlowConsistency,
      CompareCtrConsistencyWaiting,
      CompareCtrConsistencyDone,
      MuxMubi,
      MuxConsistency,
      CtrlRedun
  } countermeasure_id_e;

  rand countermeasure_id_e cm_id;

  extern task body();
  extern task wait_with_bound(int max_clks);

  extern task pick_err_inj_point(bit force_early = 1'b0);
  extern function prim_mubi_pkg::mubi4_t get_invalid_mubi4();

  // Cover all possible FSM transitions to the invalid state by triggering alerts at opportune times
  // in the comparison module.
  extern local task test_fsm_invalid_transitions();

  // Once rom_ctrl has handed control of the mux to the bus, the internal FSM counter should point
  // at the top of ROM. The unexpected_counter_change signal in rom_ctrl_fsm goes high and generates
  // a fatal alert if that counter is perturbed in any way. To test this, corrupt the counter's
  // address to some value other than the ROM's top address.
  extern local task test_counter_consistency();

  // The main checker FSM steps on internal 'done' signals, coming from its address counter, the
  // KMAC response and its comparison counter. If any of these are asserted at times we don't
  // expect, the FSM jumps to an invalid state. This triggers an alert and will not set the external
  // 'done' signal for pwrmgr to continue boot.
  extern local task test_checker_ctrl_flow_consistency();

  // The checker runs when its start_i signal goes high. If an attacker managed to poke this early,
  // they might manage to do so before there KMAC had reported a digest or we had read the expected
  // digest. It would then check that 0 == 0, and we'd lose any security from the check.
  //
  // To make sure this doesn't happen, the FSM requires that the "checker done" signal only goes
  // high when the FSM is in a state where we expect to have started it. This task starts the
  // checker early. 8 cycles later, we expect it to report completion and the FSM check will fail,
  // locking up the FSM and raising an alert.
  extern local task run_compare_early();

  // Force a counter inside the hash comparison module to a nonzero value before the comparison
  // starts. An attacker doing so could avoid checking some of the words in the digests. Check that
  // the comparison module spots the problem and generates a fatal error.
  extern local task corrupt_compare_counter_early();

  // Force the state_q signal in the hash comparison module to be "Done" before the counter gets to
  // LastAddr. An attacker doing so could avoid checking some of the words in the digests (by
  // skipping one or more at the end). The comparison module is supposed to spot when this has
  // happened. Check it does so and generates a fatal error.
  extern local task corrupt_compare_state();

  // Corrupt the mubi4 signal that selects between the FSM and bus access. This should be caught and
  // trigger a fatal alert. Testing the mux select slightly further, also try to corrupt its
  // sel_bus_qq signal (which is a registered version of the first signal, used to check for
  // "roll-back" attacks).
  extern local task corrupt_mux_select_signals();

  // The mux that chooses between the checker and the bus is supposed to be "one way" and will
  // generate a fatal alert if it switches back again. Wait for the mux to switch to the bus, then
  // force it back to the checker and check that an alert comes out.
  extern local task corrupt_select_from_bus_to_checker();

  // Inject errors into bus_rom_rom_index (which is how an attacker would get a different memory
  // word) and then check that the data that gets read doesn't match the data stored at the glitched
  // address.
  extern local task corrupt_rom_address();

endclass

task rom_ctrl_corrupt_sig_fatal_chk_vseq::body();
  int num_reps = 15;
  for (int i = 0; i < num_reps; i++) begin
    `DV_CHECK_STD_RANDOMIZE_FATAL(cm_id)
    `uvm_info(`gfn, $sformatf("iteration %0d/%0d, cmd_id = %s", i, num_reps, cm_id.name()),
               UVM_LOW)
    case (cm_id)
      // This test tries to cover all possible FSM transitions to the invalid state by triggering
      // an alert inside the comparison module.
      LocalEscalation: test_fsm_invalid_transitions();
      CheckerCtrConsistency: test_counter_consistency();
      CheckerCtrlFlowConsistency: test_checker_ctrl_flow_consistency();
      CompareCtrlFlowConsistency: run_compare_early();
      CompareCtrConsistencyWaiting: corrupt_compare_counter_early();
      CompareCtrConsistencyDone: corrupt_compare_state();
      MuxMubi: corrupt_mux_select_signals();
      MuxConsistency: corrupt_select_from_bus_to_checker();
      CtrlRedun: corrupt_rom_address();

      default: `uvm_fatal(`gfn, $sformatf("Bad cm_id: %0d", cm_id))
    endcase

    dut_init();

    // If we ran corrupt_rom_address, it will have forced a signal that would make
    // BusRomIndicesMatch_A fail. We turned that assertion off then, but should turn it back on
    // again now.
    $asserton(0, "tb.dut.BusRomIndicesMatch_A");
  end
endtask : body

task rom_ctrl_corrupt_sig_fatal_chk_vseq::wait_with_bound(int max_clks);
  // Lower bound is chosen to be 2 to allow for at least 1 clock cycle after ROM check is done.
  repeat($urandom_range(2,max_clks))
    @(negedge cfg.clk_rst_vif.clk);
endtask: wait_with_bound

task rom_ctrl_corrupt_sig_fatal_chk_vseq::pick_err_inj_point(bit force_early = 1'b0);
  int wait_clks;
  bit inject_after_done;

  // Pick error injection point. 1 - After ROM check completion. 0 - Before ROM check completion.
  //
  // If there is a requirement of injecting error before ROM check completes,then
  // inject_after_done getting randomized and then set to 0 won't help.
  //
  // force_early being true, sets inject_after_done to 0 if there is a requirement to always inject
  // error before ROM check finishes.

  if (force_early) inject_after_done = 1'b0;
  else `DV_CHECK_STD_RANDOMIZE_FATAL(inject_after_done)

  if(inject_after_done) begin
    wait (cfg.rom_ctrl_vif.pwrmgr_data.done == MuBi4True);
    wait_clks = 10;
  end
  else begin
    wait_clks = 10000;
  end
  wait_with_bound(wait_clks);

  if (!inject_after_done) `DV_CHECK(cfg.rom_ctrl_vif.pwrmgr_data.done != MuBi4True)
endtask

function prim_mubi_pkg::mubi4_t rom_ctrl_corrupt_sig_fatal_chk_vseq::get_invalid_mubi4();
  // This is a bit of a hack and we're basically inlining the contents of mubi4_test_invalid. This
  // is because arguments to a function in any particular constraint get fixed before the
  // constraint is evaluated. This means that you can't use a constraint of the form "is_good(x)"
  // to ensure x is valid.
  logic [3:0] val;
  `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(val, ~(val inside {MuBi4True, MuBi4False});)
  return prim_mubi_pkg::mubi4_t'(val);
endfunction

task rom_ctrl_corrupt_sig_fatal_chk_vseq::test_fsm_invalid_transitions();
  import rom_ctrl_pkg::fsm_state_e;

  bit in_bad_state = 1'b0;
  rom_ctrl_pkg::fsm_state_e s;
  rom_ctrl_pkg::fsm_state_e states_to_visit[$];

  // There are several possible FSM states (encoded with the fsm_state_e enum) and any of them has
  // an edge to Invalid. Make a list of all of the states other than Invalid.
  s = s.first();
  forever begin
    if (s != rom_ctrl_pkg::Invalid) states_to_visit.push_back(s);
    if (s == s.last()) break;
    s = s.next();
  end

  // Now try to see each FSM state. Repeatedly wait until the FSM gets to some state that we haven't
  // ticked off, then tick that state off. This probably won't tick all the states off (for example,
  // we might not see both RomAhead and KmacAhead). To avoid getting stuck, give up after we've
  // jumped from the (normally) terminal Done state to Invalid.
  forever begin
    rom_ctrl_pkg::fsm_state_e cur_state;

    // If this is not the first time around the loop then we'll be in an Invalid state at this
    // point (and the block will be dead). Force a reset to get back into a good state.
    if (in_bad_state) dut_init();

    // If states_to_visit is empty, we have finished our work! Drop out.
    if (!states_to_visit.size()) break;

    cfg.fsm_vif.wait_for_fsm_state_inside(states_to_visit);
    cur_state = cfg.fsm_vif.get_fsm_state();

    // Pick an invalid FSM state in the compare module to trigger an alert.
    cfg.compare_vif.splat_fsm_state();
    wait_for_fatal_alert();

    in_bad_state = 1'b1;

    // Since we've jumped from cur_state, delete it from the queue
    foreach (states_to_visit[i]) begin
      if (states_to_visit[i] == cur_state) begin
        states_to_visit.delete(i);
        break;
      end
    end

    // If cur_state was Done, we must have run through the FSM to that "check complete" state
    // without hitting any of the other items in states_to_visit. There's not much point in trying
    // again: we'll just get to the same place again.
    if (cur_state == rom_ctrl_pkg::Done) break;
  end
endtask

task rom_ctrl_corrupt_sig_fatal_chk_vseq::test_counter_consistency();
  // Pick the index of some ROM word other than the top one
  int unsigned addr = $urandom_range(0, RomSizeWords - 1);

  // Wait until rom_ctrl says that it has finished computing the ROM checksum.
  wait (mubi4_test_true_strict(cfg.rom_ctrl_vif.pwrmgr_data.done));

  // Now wait slightly longer (so we're not messing around with stuff at exactly the moment it
  // finishes)
  wait_with_bound(1000);

  // Set the silly address value for a cycle. This should be picked up by the counter suddenly
  // deciding it's not done and the code in rom_ctrl_fsm noticing the change.
  cfg.fsm_vif.force_counter_addr(addr);

  // Wait for a fatal alert to come out, to make sure that the dut notices the corruption
  wait_for_fatal_alert();
endtask

task rom_ctrl_corrupt_sig_fatal_chk_vseq::test_checker_ctrl_flow_consistency();
  for (int unsigned i = 0; i < 3; i++) begin
    // If this isn't the first iteration, the previous iteration will have left things in an invalid
    // state. Reset to tidy up.
    if (i > 0) dut_init();

    // Wait a short time (so that we don't corrupt the signal straight after reset)
    wait_with_bound(100);

    // Force the relevant "done" signal
    case (i)
      0: cfg.rom_ctrl_vif.force_kmac_data_done();
      1: cfg.fsm_vif.force_checker_done();
      2: cfg.fsm_vif.force_counter_done();
      default: `uvm_fatal(`gfn, "bad index!")
    endcase

    // This should cause the dut to notice the bad control flow and raise an alert. Wait for that to
    // happen.
    wait_for_fatal_alert();
  end
endtask

task rom_ctrl_corrupt_sig_fatal_chk_vseq::run_compare_early();
  virtual alert_esc_if alert_vif = cfg.m_alert_agent_cfgs["fatal"].vif;

  // Wait a short time (to avoid always starting at exactly the start)
  wait_with_bound(100);

  // If there's a ping in flight wait until it's finished. Otherwise, the alert due to the fault
  // injection may be hard to predict since it will come after the ping, but dependant on the exact
  // ping timing
  if (alert_vif.in_ping_st()) begin
    // There's 2-cycles sampling delay in the monitor, so if the VIF has already seen the ping Wait
    // for it. Otherwise there may be scenarios where the `active_ping` is not yet set in the
    // monitor due to the 2-cycle delay. Which causes issues predicting the value in
    // `fatal_alert_cause`
    wait (cfg.m_alert_agent_cfgs["fatal"].active_ping == 1);
  end
  wait (cfg.m_alert_agent_cfgs["fatal"].active_ping == 0);

  // Forcing this signal is (obviously) only going to work if we are still early enough. Snoop
  // quickly on the FSM state and check that it is ReadingLow (meaning we're pretty certain that if
  // we start it now, the checker will finish its job before the FSM is ready for it).
  `DV_CHECK(cfg.fsm_vif.get_fsm_state() == rom_ctrl_pkg::ReadingLow)

  // Start an early check
  cfg.fsm_vif.force_checker_start();

  wait_for_fatal_alert();
endtask

task rom_ctrl_corrupt_sig_fatal_chk_vseq::corrupt_compare_counter_early();
  bit [2:0] aw, addr;

  // Wait a short time (to avoid always starting at exactly the start)
  wait_with_bound(100);

  // Check that the compare module is still waiting to be told to start. Note that this needs a
  // "magic value" (because the indices of the sparse FSM are internal to the design). If it changes
  // in the future, this check will fail and we can pull the enum declaration to rom_ctrl_pkg.
  `DV_CHECK(cfg.compare_vif.is_waiting())

  // Now poke the address to some nonzero value
  aw = cfg.compare_vif.get_AW();
  `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(addr, addr > 0; (addr >> aw) == 0;)
  cfg.compare_vif.force_addr_q(addr);

  // This should be noticed!
  wait_for_fatal_alert();
endtask

task rom_ctrl_corrupt_sig_fatal_chk_vseq::corrupt_compare_state();
  // Randomly pick an early moment to force the comparison module to be "done" (when it's just about
  // to check a word before the last one).
  //
  // The "-2" is because the RTL doesn't spot an attack that claims "done" on the last word
  // (claiming it a cycle early), because the check ends up running when we are claiming "done" and
  // the counter points at the last word. The security risk of this is low though: a putative
  // attacker would have to find a collision for all the other words of the SHA3 hash.
  int unsigned injection_point = $urandom_range(0, cfg.compare_vif.get_last_addr() - 2);

  // Wait until the comparison module is about has got to that point, stepping on negedges to be in
  // the "middle of the cycle".
  cfg.compare_vif.wait_addr_q(injection_point);

  // Force the compare FSM's state to 'Done'.
  cfg.compare_vif.set_fsm_done();

  // This "early completion" should be spotted. Check that it is.
  wait_for_fatal_alert();
endtask

task rom_ctrl_corrupt_sig_fatal_chk_vseq::corrupt_mux_select_signals();
  pick_err_inj_point();
  cfg.fsm_vif.force_rom_select_bus_o(get_invalid_mubi4());
  wait_for_fatal_alert(.check_fsm_state(1'b0));
  dut_init();

  pick_err_inj_point(1'b1);
  cfg.rom_ctrl_vif.override_sel_bus_qq(get_invalid_mubi4());
  wait_for_fatal_alert(.check_fsm_state(1'b0));
endtask

task rom_ctrl_corrupt_sig_fatal_chk_vseq::corrupt_select_from_bus_to_checker();
  wait (cfg.rom_ctrl_vif.pwrmgr_data.done == MuBi4True);
  wait_with_bound(10);
  cfg.fsm_vif.force_rom_select_bus_o(MuBi4False);
  wait_for_fatal_alert(.check_fsm_state(1'b0));
endtask

task rom_ctrl_corrupt_sig_fatal_chk_vseq::corrupt_rom_address();
  addr_range_t loc_mem_range[$] = cfg.ral_models["rom_ctrl_prim_reg_block"].mem_ranges;
  bit [TL_DW-1:0] rdata, rdata_tgt, corr_data;
  bit [TL_AW-1:0] addr;
  int             mem_idx = $urandom_range(0, loc_mem_range.size - 1);
  bit [12:0]      bus_rom_rom_index_val;
  bit [12:0]      corr_bus_rom_rom_index_val;
  bit [TL_AW-1:0] tgt_addr;
  cip_tl_seq_item tl_access_rsp;
  bit             completed, saw_err;
  string          path;

  wait (cfg.rom_ctrl_vif.pwrmgr_data.done == MuBi4True);
  wait_with_bound(10);
  `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(addr,
                                     addr inside {[loc_mem_range[mem_idx].start_addr :
                                     loc_mem_range[mem_idx].end_addr]};)
  bus_rom_rom_index_val = addr[2 +: RomIndexWidth];
  `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(tgt_addr,
                                     tgt_addr inside {[loc_mem_range[mem_idx].start_addr :
                                     loc_mem_range[mem_idx].end_addr]};
                                     (tgt_addr != addr);)
  corr_bus_rom_rom_index_val = tgt_addr[2 +: RomIndexWidth];
  tl_access_sub(.addr(addr), .write(0), .data(rdata), .completed(completed),
                .saw_err(saw_err), .check_rsp(1), .rsp(tl_access_rsp),
                .tl_sequencer_h(p_sequencer.tl_sequencer_hs["rom_ctrl_prim_reg_block"]));
  void'(tl_access_rsp.is_d_chan_intg_ok(.en_rsp_intg_chk(1),
                                        .en_data_intg_chk(1),
                                        .throw_error(1)));
  tl_access_sub(.addr(tgt_addr), .write(0), .data(rdata_tgt), .completed(completed),
                .saw_err(saw_err), .check_rsp(1), .rsp(tl_access_rsp),
                .tl_sequencer_h(p_sequencer.tl_sequencer_hs["rom_ctrl_prim_reg_block"]));
  void'(tl_access_rsp.is_d_chan_intg_ok(.en_rsp_intg_chk(1),
                                        .en_data_intg_chk(1),
                                        .throw_error(1)));

  $assertoff(0, "tb.dut.BusRomIndicesMatch_A");
  fork
    begin
      cfg.en_scb_tl_err_chk = 0;
      cfg.scoreboard.disable_rom_acc_chk = 1;
      tl_access_sub(.addr(addr), .write(0), .data(corr_data), .completed(completed),
                    .saw_err(saw_err), .check_rsp(1), .rsp(tl_access_rsp),
                    .tl_sequencer_h(p_sequencer.tl_sequencer_hs["rom_ctrl_prim_reg_block"])
                   );
      `DV_CHECK_EQ(completed, 1)
      `DV_CHECK_EQ(saw_err, 0)
      if ((corr_data == rdata) || (corr_data == rdata_tgt)) begin
        `uvm_error(`gfn, "corr_data matching data in rom")
      end
      cfg.en_scb_tl_err_chk = 1;
      cfg.scoreboard.disable_rom_acc_chk = 0;
    end
    begin
      cfg.rom_ctrl_vif.override_bus_rom_index(corr_bus_rom_rom_index_val);
    end
  join
endtask
