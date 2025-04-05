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
  extern task force_sig(string path, int value);
  extern task chk_fsm_state();

  // Wait until the FSM state is a value in the queue. When that happens, write that state to
  // state_seen.
  extern local task wait_for_fsm_state_inside(rom_ctrl_pkg::fsm_state_e        states_to_visit[$],
                                              output rom_ctrl_pkg::fsm_state_e state_seen);

  extern task pick_err_inj_point(bit force_early = 1'b0);
  extern function prim_mubi_pkg::mubi4_t get_invalid_mubi4();

  // Cover all possible FSM transitions to the invalid state by triggering alerts at opportune times
  // in the comparison module.
  extern local task test_fsm_invalid_transitions();

endclass : rom_ctrl_corrupt_sig_fatal_chk_vseq

task rom_ctrl_corrupt_sig_fatal_chk_vseq::body();
  int num_reps;
  `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(num_reps, (num_reps >= 10  && num_reps <= 20);)
  for (int i = 0; i < num_reps; i++) begin
    `DV_CHECK_STD_RANDOMIZE_FATAL(cm_id)
    `uvm_info(`gfn, $sformatf("iteration %0d/%0d, cmd_id = %s", i, num_reps, cm_id.name()),
               UVM_LOW)
    case (cm_id)
      // This test tries to cover all possible FSM transitions to the invalid state by triggering
      // an alert inside the comparison module.
      LocalEscalation: test_fsm_invalid_transitions();

      // Once rom_ctrl has handed control of the mux to the bus, the internal FSM counter should
      // point at the top of ROM. The unexpected_counter_change signal in rom_ctrl_fsm goes high
      // and generates a fatal alert if that counter is perturbed in any way. To test this,
      // addr_q in the counter is corrupted with any value other than the ROM's top address.
      CheckerCtrConsistency: begin
        bit [12:0] invalid_addr;
        wait (mubi4_test_true_strict(cfg.rom_ctrl_vif.pwrmgr_data.done));
        wait_with_bound(10000);
        // Pick the index of a ROM word other than the top one
        `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(invalid_addr, (invalid_addr < (RomSizeWords-1)););
        force_sig("tb.dut.gen_fsm_scramble_enabled.u_checker_fsm.u_counter.addr_q", invalid_addr);
        wait_for_fatal_alert();
      end
      // The main checker FSM steps on internal 'done' signals, coming from its address counter,
      // the KMAC response and its comparison counter. If any of these are asserted at times we
      // don't expect, the FSM jumps to an invalid state. This triggers an alert and will not set
      // the external 'done' signal for pwrmgr to continue boot.
      CheckerCtrlFlowConsistency: begin
        wait_with_bound(100);
        force_sig("tb.dut.kmac_data_i.done", 1);
        wait_for_fatal_alert();
        dut_init();
        wait_with_bound(100);
        force_sig("tb.dut.gen_fsm_scramble_enabled.u_checker_fsm.checker_done", 1);
        wait_for_fatal_alert();
        dut_init();
        wait_with_bound(100);
        force_sig("tb.dut.gen_fsm_scramble_enabled.u_checker_fsm.counter_done", 1);
        wait_for_fatal_alert();
      end
      // The main checker FSM steps on internal 'done' signals, coming from its address counter,
      // the KMAC response and its comparison counter. If any of these are asserted at times
      // we don't expect, the FSM jumps to an invalid state. This triggers an alert and will not
      // set the external 'done' signal for pwrmgr to continue boot. To test this start_checker_q
      // signal from rom_ctrl_fsm is asserted randomly.
      CompareCtrlFlowConsistency: begin
        string start_chk_path = "tb.dut.gen_fsm_scramble_enabled.u_checker_fsm.start_checker_q";
        bit rdata;
        // VIF declared for easier readability
        virtual alert_esc_if alert_vif = cfg.m_alert_agent_cfgs["fatal"].vif;
        pick_err_inj_point();
        // If there's a ping on-flight wait until it's finished. Otherwise, the alert due to the
        // fault injection may be hard to predict since it will come after the ping, but
        // dependant on the exact ping timing
        if (alert_vif.in_ping_st()) begin
          // There's 2-cycles sampling delay in the monitor, so if the VIF has already seen the ping
          // Wait for it. Otherwise there may be scenarios where the `active_ping` is not yet set
          // in the monitor due to the 2-cycle delay. Which causes issues predicting the value in
          // `fatal_alert_cause`
          wait (cfg.m_alert_agent_cfgs["fatal"].active_ping == 1);
        end
        wait (cfg.m_alert_agent_cfgs["fatal"].active_ping == 0);

        do begin
          `DV_CHECK(uvm_hdl_read(start_chk_path, rdata))
          @(posedge cfg.clk_rst_vif.clk);
        end while (rdata != 0);
        force_sig(start_chk_path, 1'b1);
        wait_for_fatal_alert();
      end
      // The hash comparison module has an internal count. If this glitches to a nonzero value
      // before the comparison starts (state=Waiting) or to a value other than the last index
      // after the comparison ends (state=Done) then a fatal alert is generated.
      // Each of these cases are covered in cases "CompareCtrConsistencyWaiting" and
      // "CompareCtrConsistencyDone"
      CompareCtrConsistencyWaiting: begin
        bit [2:0] invalid_addr;
        bit [4:0] fsm_state_q;
        string    path;
        wait_with_bound(2000);
        path = "tb.dut.gen_fsm_scramble_enabled.u_checker_fsm.u_compare.state_q";
        `DV_CHECK(uvm_hdl_read(path,fsm_state_q));
        if(fsm_state_q != 5'b00100) begin
          `uvm_fatal(`gfn, {"Case:'CompareCtrConsistencyWaiting' hit when 'rom_ctrl_compare' ",
                            "state!=Done hence sequence-case exits"})
        end
        // State == Waiting -> It's ok to poke the addr_q to be non-zero
        `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(invalid_addr, invalid_addr > 0;);
        force_sig("tb.dut.gen_fsm_scramble_enabled.u_checker_fsm.u_compare.addr_q",
                  invalid_addr);
        wait_for_fatal_alert();
        dut_init();
      end
      CompareCtrConsistencyDone: begin
        bit [2:0] invalid_addr;

        wait (cfg.rom_ctrl_vif.pwrmgr_data.done == MuBi4True);
        // After cfg.rom_ctrl_vif.pwrmgr_data.done = True we're in Done state
        wait_with_bound(10);
        // LastAddr has been set to 7
        `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(invalid_addr, invalid_addr < 7;);
        force_sig("tb.dut.gen_fsm_scramble_enabled.u_checker_fsm.u_compare.addr_q", invalid_addr);
        wait_for_fatal_alert();
      end
      // The mux that arbitrates between the checker and the bus is multi-bit encoded.
      // An invalid value generates a fatal alert with the sel_invalid signal in the rom_ctrl_mux
      // module. To test this rom_select_bus_o is forced with any value other than MuBi4True and
      // MuBi4False.
      MuxMubi: begin
        pick_err_inj_point();
        force_sig("tb.dut.gen_fsm_scramble_enabled.u_checker_fsm.rom_select_bus_o",
                  get_invalid_mubi4());
        wait_for_fatal_alert(.check_fsm_state(1'b0));
        dut_init();
        pick_err_inj_point(1'b1);
        force_sig("tb.dut.u_mux.sel_bus_qq", get_invalid_mubi4());
        wait_for_fatal_alert(.check_fsm_state(1'b0));
      end
      // The mux that arbitrates between the checker and the bus gives access to the checker at
      // the start of time and then switches to the bus, never going back. If a glitch does cause
      // it to switch back, a fatal alert is generated with the sel_reverted or sel_q_reverted
      // signals in the rom_ctrl_mux module. To test this rom_select_bus_o is forced to
      // MuBi4False after rom check is completed.
      MuxConsistency: begin
        wait (cfg.rom_ctrl_vif.pwrmgr_data.done == MuBi4True);
        wait_with_bound(10);
        force_sig("tb.dut.gen_fsm_scramble_enabled.u_checker_fsm.rom_select_bus_o", MuBi4False);
        wait_for_fatal_alert(.check_fsm_state(1'b0));
      end
      // Inject errors into bus_rom_rom_index (which is how an attacker would get a different
      // memory word) and then check that the data that gets read doesn't match the data stored
      // at the glitched address.
      CtrlRedun: begin
        addr_range_t loc_mem_range[$] = cfg.ral_models["rom_ctrl_prim_reg_block"].mem_ranges;
        bit [TL_DW-1:0] rdata, rdata_tgt, corr_data;
        bit [TL_AW-1:0] addr;
        int             mem_idx = $urandom_range(0, loc_mem_range.size - 1);
        bit [12:0]      bus_rom_rom_index_val;
        bit [12:0]      corr_bus_rom_rom_index_val;
        bit [TL_AW-1:0]      tgt_addr;
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
            string rom_idx_path = "tb.dut.bus_rom_rom_index";

            wait (cfg.m_tl_agent_cfgs["rom_ctrl_prim_reg_block"].vif.h2d.a_valid);
            $assertoff(0, "tb.dut.BusRomIndicesMatch_A");
            `DV_CHECK(uvm_hdl_force(rom_idx_path, corr_bus_rom_rom_index_val));
            wait (!cfg.m_tl_agent_cfgs["rom_ctrl_prim_reg_block"].vif.h2d.a_valid);
            `DV_CHECK(uvm_hdl_release(rom_idx_path));
          end
        join
      end
      default: begin
        // do nothing
      end
    endcase
    wait_with_bound(10);
    dut_init();
    $asserton(0, "tb.dut.BusRomIndicesMatch_A");
  end
endtask : body

task rom_ctrl_corrupt_sig_fatal_chk_vseq::wait_with_bound(int max_clks);
  // Lower bound is chosen to be 2 to allow for at least 1 clock cycle after ROM check is done.
  repeat($urandom_range(2,max_clks))
    @(negedge cfg.clk_rst_vif.clk);
endtask: wait_with_bound

task rom_ctrl_corrupt_sig_fatal_chk_vseq::force_sig(string path, int value);
  `DV_CHECK(uvm_hdl_force(path, value));
  `uvm_info(`gfn, $sformatf("Setting path: %s to value=0x%0x",path,value), UVM_DEBUG)
  @(negedge cfg.clk_rst_vif.clk);
  `DV_CHECK(uvm_hdl_release(path));
endtask: force_sig

task rom_ctrl_corrupt_sig_fatal_chk_vseq::chk_fsm_state();
  string alert_o_path = "tb.dut.gen_fsm_scramble_enabled.u_checker_fsm.alert_o";
  string state_q_path = "tb.dut.gen_fsm_scramble_enabled.u_checker_fsm.state_q";
  bit rdata_alert;
  bit [$bits(rom_ctrl_pkg::fsm_state_e)-1:0] rdata_state;

  `DV_CHECK_EQ(rdata_state, rom_ctrl_pkg::Invalid)
endtask: chk_fsm_state

task
  rom_ctrl_corrupt_sig_fatal_chk_vseq::
    wait_for_fsm_state_inside(rom_ctrl_pkg::fsm_state_e        states_to_visit[$],
                              output rom_ctrl_pkg::fsm_state_e state_seen);
  string state_q_path = "tb.dut.gen_fsm_scramble_enabled.u_checker_fsm.state_q";
  bit [$bits(rom_ctrl_pkg::fsm_state_e)-1:0] raw_state;

  // Step through the middles of cycles until the FSM state is in the list of states to visit.
  do begin
    @(negedge cfg.clk_rst_vif.clk);
    `DV_CHECK(uvm_hdl_read(state_q_path, raw_state))
  end while (!(raw_state inside {states_to_visit}));

  state_seen = rom_ctrl_pkg::fsm_state_e'(raw_state);
endtask

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

    wait_for_fsm_state_inside(states_to_visit, cur_state);

    // This is a sparsely encoded FSM where all-zero is always an invalid state. So we can pick that
    // value to trigger an alert.
    force_sig("tb.dut.gen_fsm_scramble_enabled.u_checker_fsm.u_compare.state_d", '0);
    wait_for_fatal_alert();

    in_bad_state = 1'b1;

    // Since we've jumped from cur_state, delete it from the queue
    for (int unsigned i = 0; i < states_to_visit.size(); i++) begin
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
