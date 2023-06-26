// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rom_ctrl_corrupt_sig_fatal_chk_vseq extends rom_ctrl_base_vseq;
  `uvm_object_utils(rom_ctrl_corrupt_sig_fatal_chk_vseq)

  `uvm_object_new

  localparam int unsigned RomSizeWords = rom_ctrl_reg_pkg::ROM_CTRL_ROM_SIZE >> 2;
  localparam int unsigned RomIndexWidth = prim_util_pkg::vbits(RomSizeWords);

  typedef enum bit [2:0] {
      LocalEscalation,
      CheckerCtrConsistency,
      CheckerCtrlFlowConsistency,
      CompareCtrlFlowConsistency,
      CompareCtrConsistency,
      MuxMubi,
      MuxConsistency,
      CtrlRedun
  } countermeasure_id_e;
  rand countermeasure_id_e cm_id;


  task body();
    int num_reps;
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(num_reps, (num_reps >= 10  && num_reps <= 20);)
    for (int i = 0; i < num_reps; i++) begin
      `DV_CHECK_STD_RANDOMIZE_FATAL(cm_id)
      `uvm_info(`gfn, $sformatf("iteration %0d/%0d, cmd_id = %s", i, num_reps, cm_id.name()),
                 UVM_LOW)
      case (cm_id)
        // This test tries to cover all possible FSM transitions to the invalid state by triggering
        // an alert inside the comparison module.
        LocalEscalation: begin
          rom_ctrl_pkg::fsm_state_e s;
          rom_ctrl_pkg::fsm_state_e states_to_visit[$];
          // This FSM assumes a linear progression through the FSM states.
          // Make sure the last state is the Invalid state.
          `DV_CHECK_EQ(s.last(), rom_ctrl_pkg::Invalid)
          s = s.first();
          while (s != s.last()) begin
            states_to_visit.push_back(s);
            s = s.next();
          end
          while (states_to_visit.size() > 0) begin
            wait_for_fsm_state_inside(states_to_visit);
            // This is a sparsely encoded FSM, where all-zero is always an invalid state, hence we
            // can use all-zero to trigger an alert.
            force_sig("tb.dut.gen_fsm_scramble_enabled.u_checker_fsm.u_compare.state_d", '0);
            check_for_alert();
            chk_fsm_state();
            dut_init();
          end
        end
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
          check_for_alert();
          chk_fsm_state();
        end
        // The main checker FSM steps on internal 'done' signals, coming from its address counter,
        // the KMAC response and its comparison counter. If any of these are asserted at times we
        // don't expect, the FSM jumps to an invalid state. This triggers an alert and will not set
        // the external 'done' signal for pwrmgr to continue boot.
        CheckerCtrlFlowConsistency: begin
          wait_with_bound(100);
          force_sig("tb.dut.kmac_data_i.done", 1);
          check_for_alert();
          chk_fsm_state();
          dut_init();
          wait_with_bound(100);
          force_sig("tb.dut.gen_fsm_scramble_enabled.u_checker_fsm.checker_done", 1);
          check_for_alert();
          chk_fsm_state();
          dut_init();
          wait_with_bound(100);
          force_sig("tb.dut.gen_fsm_scramble_enabled.u_checker_fsm.counter_done", 1);
          check_for_alert();
          chk_fsm_state();
        end
        // The main checker FSM steps on internal 'done' signals, coming from its address counter,
        // the KMAC response and its comparison counter. If any of these are asserted at times
        // we don't expect, the FSM jumps to an invalid state. This triggers an alert and will not
        // set the external 'done' signal for pwrmgr to continue boot. To test this start_checker_q
        // signal from rom_ctrl_fsm is asserted randomly.
        CompareCtrlFlowConsistency: begin
          bit rdata;
          pick_err_inj_point();
          do begin
            uvm_hdl_read("tb.dut.gen_fsm_scramble_enabled.u_checker_fsm.start_checker_q", rdata);
            @(posedge cfg.clk_rst_vif.clk);
          end while (rdata != 0);
          force_sig("tb.dut.gen_fsm_scramble_enabled.u_checker_fsm.start_checker_q", 1'b1);
          check_for_alert();
          chk_fsm_state();
        end
        // The hash comparison module has an internal count. If this glitches to a nonzero value
        // before the comparison starts or to a value other than the last index after the
        // comparison ends then a fatal alert is generated.
        CompareCtrConsistency: begin
          bit [2:0] invalid_addr;
          wait_with_bound(10000);
          `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(invalid_addr, invalid_addr > 0;);
          force_sig("tb.dut.gen_fsm_scramble_enabled.u_checker_fsm.u_compare.addr_q",
                    invalid_addr);
          check_for_alert();
          chk_fsm_state();
          dut_init();
          wait (cfg.rom_ctrl_vif.pwrmgr_data.done == MuBi4True);
          wait_with_bound(10);
          // LastAddr has been set to 7
          `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(invalid_addr,
                                             (invalid_addr >= 0 && invalid_addr < 7););
          force_sig("tb.dut.gen_fsm_scramble_enabled.u_checker_fsm.u_compare.addr_q", invalid_addr);
          check_for_alert();
          chk_fsm_state();
        end
        // The mux that arbitrates between the checker and the bus is multi-bit encoded.
        // An invalid value generates a fatal alert with the sel_invalid signal in the rom_ctrl_mux
        // module. To test this rom_select_bus_o is forced with any value other than MuBi4True and
        // MuBi4False.
        MuxMubi: begin
          bit [3:0] rand_var;
          pick_err_inj_point();
          mubi4_test_invalid(prim_mubi_pkg::mubi4_t'(rand_var));
          force_sig("tb.dut.gen_fsm_scramble_enabled.u_checker_fsm.rom_select_bus_o", rand_var);
          check_for_alert();
          dut_init();
          pick_err_inj_point();
          mubi4_test_invalid(prim_mubi_pkg::mubi4_t'(rand_var));
          force_sig("tb.dut.u_mux.sel_bus_q", rand_var);
          check_for_alert();
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
          check_for_alert();
        end
        // Inject errors into bus_rom_rom_index (which is how an attacker would get a different
        // memory word) and then check that the data that gets read doesn't match the data stored
        // at the glitched address.
        CtrlRedun: begin
          addr_range_t loc_mem_range[$] = cfg.ral_models["rom_ctrl_rom_reg_block"].mem_ranges;
          bit [TL_DW-1:0] rdata, rdata_tgt, corr_data;
          bit [TL_AW-1:0] addr;
          int             mem_idx = $urandom_range(0, loc_mem_range.size - 1);
          bit [12:0]      bus_rom_rom_index_val;
          bit [12:0]      corr_bus_rom_rom_index_val;
          bit [TL_AW-1:0]      tgt_addr;
          cip_tl_seq_item tl_access_rsp;
          bit             completed, saw_err;

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
                        .tl_sequencer_h(p_sequencer.tl_sequencer_hs["rom_ctrl_rom_reg_block"]));
          void'(tl_access_rsp.is_d_chan_intg_ok(.en_rsp_intg_chk(1),
                                                .en_data_intg_chk(1),
                                                .throw_error(1)));
          tl_access_sub(.addr(tgt_addr), .write(0), .data(rdata_tgt), .completed(completed),
                        .saw_err(saw_err), .check_rsp(1), .rsp(tl_access_rsp),
                        .tl_sequencer_h(p_sequencer.tl_sequencer_hs["rom_ctrl_rom_reg_block"]));
          void'(tl_access_rsp.is_d_chan_intg_ok(.en_rsp_intg_chk(1),
                                                .en_data_intg_chk(1),
                                                .throw_error(1)));
          fork
            begin
              cfg.en_scb_tl_err_chk = 0;
              cfg.scoreboard.disable_rom_acc_chk = 1;
              tl_access_sub(.addr(addr), .write(0), .data(corr_data), .completed(completed),
                            .saw_err(saw_err), .check_rsp(1), .rsp(tl_access_rsp),
                            .tl_sequencer_h(p_sequencer.tl_sequencer_hs["rom_ctrl_rom_reg_block"])
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
              wait (cfg.m_tl_agent_cfgs["rom_ctrl_rom_reg_block"].vif.h2d.a_valid);
              $assertoff(0, "tb.dut.BusRomIndicesMatch_A");
              uvm_hdl_force("tb.dut.bus_rom_rom_index", corr_bus_rom_rom_index_val);
              wait (!cfg.m_tl_agent_cfgs["rom_ctrl_rom_reg_block"].vif.h2d.a_valid);
              uvm_hdl_release("tb.dut.bus_rom_rom_index");
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

  task check_for_alert();
    uvm_reg_data_t act_val;
    bit [31:0] pred_data;
    cfg.scoreboard.set_exp_alert("fatal", .is_fatal(1'b1), .max_delay(10000));
    fork
      begin
        pred_data = 'b1;
        ral.fatal_alert_cause.predict(.value(pred_data), .kind(UVM_PREDICT_READ), .be(4'hF));
        wait_alert_trigger ("fatal", .max_wait_cycle(1000), .wait_complete(1));
        csr_utils_pkg::csr_rd(.ptr(ral.fatal_alert_cause), .value(act_val));
      end
      begin
        repeat(3) wait_alert_trigger ("fatal", .max_wait_cycle(1000), .wait_complete(1));
      end
    join
  endtask: check_for_alert

  task wait_with_bound(int max_clks);
    // Lower bound is chosen to be 2 to allow for at least 1 clock cycle after ROM check is done.
    repeat($urandom_range(2,max_clks))
      @(negedge cfg.clk_rst_vif.clk);
  endtask: wait_with_bound

  task chk_hdl_path(string path);
    if(!uvm_hdl_check_path(path))
      begin
        `uvm_fatal("PATH NOT FOUND", $sformatf("%s", path))
      end
  endtask: chk_hdl_path

  task force_sig(string path, int value);
    chk_hdl_path(path);
    uvm_hdl_force(path, value);
    @(negedge cfg.clk_rst_vif.clk);
    uvm_hdl_release(path);
  endtask: force_sig

  task chk_fsm_state();
    bit rdata_alert;
    bit [$bits(rom_ctrl_pkg::fsm_state_e)-1:0] rdata_state;
    uvm_hdl_read("tb.dut.gen_fsm_scramble_enabled.u_checker_fsm.alert_o", rdata_alert);
    `DV_CHECK_EQ(rdata_alert, 1)
    uvm_hdl_read("tb.dut.gen_fsm_scramble_enabled.u_checker_fsm.state_q", rdata_state);
    `DV_CHECK_EQ(rdata_state, rom_ctrl_pkg::Invalid)
  endtask: chk_fsm_state

  // Wait until FSM state has progressed to a state within the list.
  // The task removes all previous states including the one that has been reached afterwards.
  // Note that this assumes no loops and linear progression through the state enum entries.
  task wait_for_fsm_state_inside(ref rom_ctrl_pkg::fsm_state_e states_to_visit[$]);
    bit [$bits(rom_ctrl_pkg::fsm_state_e)-1:0] rdata_state;
    do begin
      @(negedge cfg.clk_rst_vif.clk);
      uvm_hdl_read("tb.dut.gen_fsm_scramble_enabled.u_checker_fsm.state_q", rdata_state);
    end while (!(rdata_state inside states_to_visit));
    `uvm_info(`gfn, $sformatf("reached FSM state %x", rdata_state), UVM_LOW)
    // Remove previous states from queue, including the one that has been reached.
    while (states_to_visit.pop_front() != rdata_state);
  endtask: wait_for_fsm_state_inside

  task pick_err_inj_point();
    int wait_clks;
    // Pick error injection point. 1 - After ROM check completion. 0 - Before ROM check completion.
    bit err_point;
    `DV_CHECK_STD_RANDOMIZE_FATAL(err_point)
    if(err_point) begin
      wait (cfg.rom_ctrl_vif.pwrmgr_data.done == MuBi4True);
      wait_clks = 10;
    end
    else begin
      wait_clks = 10000;
    end
    wait_with_bound(wait_clks);
  endtask

endclass : rom_ctrl_corrupt_sig_fatal_chk_vseq
