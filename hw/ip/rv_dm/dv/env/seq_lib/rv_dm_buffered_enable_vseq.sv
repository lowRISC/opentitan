// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
//
// This sequence forces a copy of the multi-bit debug enable signal to On, enabling the feature
// enabled by that copy.
//
// Note that it's implausible that an attacker will be able to force this multi-bit signal
// directly. But there might be a single bit somewhere downstream that is attackable. Allowing the
// attacker to force at this level is a safe overapproximation of their capabilities.
//
// For some copies, the multi-bit signal gets divided into further buffered copies. For those
// copies, allowing the top multi-bit signal to be forced is going to strictly over-approximate the
// attacker's capabilities (which, of course, is perfectly safe)

class rv_dm_buffered_enable_vseq extends rv_dm_base_vseq;
  `uvm_object_utils(rv_dm_buffered_enable_vseq)
  `uvm_object_new

  // Override the constraint in rv_dm_base_vseq that enables debug (to disable it instead)
  constraint debug_enabled_c {
    lc_hw_debug_en == 1'b0;
  }

  // (Shortened versions of) the names of the buffered copies of the debug enable signal.
  typedef enum { Fetch, Rom, Sba, DebugReq, ResetReq } copy_t;

  // The index of the buffered copy of the signal to force.
  rand copy_t tgt_copy;

  function string enable_path_at(copy_t copy);
    return $sformatf("tb.dut.u_lc_en_sync_copies.gen_buffs[%0d].lc_en_out", copy);
  endfunction

  task force_enable_at(copy_t copy);
    `DV_CHECK(uvm_hdl_force(enable_path_at(copy), lc_ctrl_pkg::On))

    // Wait a few cycles to allow any newly enabled copies to propagate through and for the LC gate
    // FSMs to get back to Active.
    cfg.clk_rst_vif.wait_clks(4);
  endtask

  task release_enable_at(copy_t copy);
    `DV_CHECK(uvm_hdl_release(enable_path_at(copy)))

    // Wait a few cycles to allow the (now cleared) enable flag for the given copy to propagate
    // through (making sure that an operation that starts after this task is complete will be
    // blocked)
    cfg.clk_rst_vif.wait_clks(4);
  endtask

  // Try to access the functionality gated by the requested copy of the enable signal. Assert that
  // the feature is accessible iff copy equals tgt_copy. Checking that a feature *is* enabled on a
  // match is a way to check there is no bug in the test, so we would notice if we would see
  // cross-enable behaviour if the two copies did not match.
  task check_copy(copy_t copy);
    case (copy)
      Fetch: check_fetch();
      Rom:   check_rom();
      Sba:   check_sba();
      DebugReq: check_debug_req();
      ResetReq: check_reset_req();
      default: `uvm_fatal(`gfn, "Unknown copy index")
    endcase
  endtask

  // Check whether it is possible to do TL fetches from the debug module's ROM. This should only be
  // possible if tgt_copy == Fetch
  task check_fetch();
    uvm_reg_addr_t mem_base_addr = tl_mem_ral.default_map.get_base_addr();
    string enable_path = $sformatf("tb.dut.lc_hw_debug_en_gated_raw[%0d]", Rom);

    // The Fetch copy is probably more secure than we need: *all* TL access will be disallowed by
    // the Rom copy being false, even if the Fetch copy is forced to true. We can make the attacker
    // even more powerful by also forcing the Rom copy to be true in every situation. Unless
    // tgt_copy is Fetch, the fetch request should still fail.
    bit also_enable_rom = (tgt_copy != Rom);

    // This is going to be a sequence that runs a single TL transaction
    cip_tl_host_single_seq seq;
    `uvm_create_on(seq, p_sequencer.tl_sequencer_hs["rv_dm_mem_reg_block"])

    if (also_enable_rom) begin
      force_enable_at(Rom);
    end

    // We want to send a TL request to fetch WHERETO. If fetching is enabled, this should respond
    // with a JAL to some address (tested by rv_dm_halt_resume_whereto_vseq). If not, we have just
    // forced the TL connection to work so we should manage to perform the TL transaction, but it
    // will respond with an error.
    //
    // Randomise the sequence, but setting instr_type (so that this is a fetch), zeroing delays (no
    // need to wait!), making the chance of abortion zero and reading from the correct address
    // (0x300 within the block).
    seq.min_req_delay = 0;
    seq.max_req_delay = 0;
    `DV_CHECK_RANDOMIZE_WITH_FATAL(seq,
                                   write == 1'b0; addr == 'h300 + mem_base_addr; mask == 4'hf;
                                   instr_type == prim_mubi_pkg::MuBi4True;)

    csr_utils_pkg::increment_outstanding_access();
    `DV_SPINWAIT(`uvm_send_pri(seq, 100), "Timed out when sending fetch request")
    csr_utils_pkg::decrement_outstanding_access();

    // At this point, the TL transaction should have completed and the response will be in seq.rsp.
    // The fetch was successful if d_error is false. This should happen exactly when we've enabled
    // the Fetch copy.
    `DV_CHECK(seq.rsp.d_error == !(tgt_copy == Fetch))

    if (also_enable_rom) begin
      release_enable_at(Rom);
    end
  endtask

  // Check whether it is possible to do any sort of TL reads from the memory window of the debug
  // module. This should only be possible if tgt_copy == Rom.
  task check_rom();
    uvm_reg_data_t rdata;
    bit restore_tl_error_checks = 1'b0;

    csr_rd(.ptr(tl_mem_ral.abstractcmd[0]), .value(rdata));

    // We've just read from abstractcmd[0]. This should be a 32-bit instruction, so not '1.
    // That will be reflected in rdata unless TL access was blocked. In that case, the tlul_lc_gate
    // responds with '1.
    `DV_CHECK_EQ(rdata != 32'hffffffff, tgt_copy == Rom)
  endtask

  // Check whether it is possible for an SBA access to cause the sba_tl_h_o signal to have
  // a_valid=1. If the Sba copy of the enable flag is not On, this should never happen. If it is
  // forced to On, it can happen. As a test of the check, we actually expect the access to complete
  // in this situation (reading a register).
  task check_sba();
    sba_access_item item = sba_access_item::type_id::create("sba_req");
    bit tl_finished, saw_a_valid;

    // Construct a single arbitrary system bus access, reading from a known-good address in the
    // block (picking arbirarily, we know that LATE_DEBUG_ENABLE should be readable over TL)
    item.bus_op = BusOpRead;
    item.size = SbaAccessSize32b;
    item.addr = ral.late_debug_enable.get_address(ral.default_map);
    item.readonaddr = 1'b1;
    item.readondata = 1'b0;

    fork
      // Send the system bus access item.
      begin
        sba_tl_device_seq_start();
        cfg.debugger.sba_access(item);
        sba_tl_device_seq_stop();
        tl_finished = 1'b1;
      end
      // Spot if a_valid goes high
      begin
        wait(cfg.m_tl_sba_agent_cfg.vif.h2d.a_valid || tl_finished);
        saw_a_valid = cfg.m_tl_sba_agent_cfg.vif.h2d.a_valid;
      end
    join

    // The bus access will always complete but it should only have caused a_valid to go high if the
    // Sba copy of the enable flag has been forced. Check this is true (and check that it *did* go
    // high if we forced that enable flag).
    `DV_CHECK_EQ(saw_a_valid, tgt_copy == Sba)
  endtask

  // Check whether it is possible to send a debug request from the debug module to the rest of the
  // system.
  //
  // We're slightly cheating here because causing the debug request itself requires us to convince
  // the debug module to actually produce the request. This is difficult when some other things are
  // disabled, so we actually force an output from dm_top and just check that it doesn't make it to
  // the top-level pin.
  task check_debug_req();
    // If tgt_copy is DebugReq, expect the debug request to be passed through. This will actually
    // cause an assertion to fail in rv_dm_enable_checker, because that module bases its check on
    // the initial single debug enable signal and doesn't know that we're overriding this copy.
    // Disable the assertion.
    $assertoff(0, "tb.dut.enable_checker.DebugRequestNeedsDebug_A");

    check_connection("u_dm_top.debug_req_o", "debug_req_o", 1'b1, tgt_copy == DebugReq);

    $asserton(0, "tb.dut.enable_checker.DebugRequestNeedsDebug_A");
  endtask

  // Check whether it is possible to send an ndmreset request from the debug module to the rest of
  // the system.
  //
  // As with check_debug_req, we're slightly cheating and force an output from dm_top and check that
  // it doesn't make it to the top-level pin.
  task check_reset_req();
    // Note that the structure of the design means that an ndmreset request will only be exposed at
    // top-level if the Rom copy is also enabled. As such, the ndmreset_req_o signal (which is the
    // only visible output outside of the block) will never go high when only one copy is enabled.
    check_connection("u_dm_top.ndmreset_o", "ndmreset_req_o", 1'b1, 1'b0);
  endtask

  // Check whether a signal can flow from in_path to out_path. This should happen in at most 100
  // cycles if is_connected is true. If not, the output shouldn't become in_value in that time.
  //
  // Both paths are relative to the top of rv_dm.
  task check_connection(string in_path, string out_path, bit in_value, bit is_connected);
    uvm_reg_data_t out_value;
    string         abs_in_path = {"tb.dut.", in_path};
    string         abs_out_path = {"tb.dut.", out_path};

    // First check that the output hasn't already been set to the value we're trying to shove
    // through the connection.
    `DV_CHECK(uvm_hdl_read(abs_out_path, out_value))
    `DV_CHECK_NE(out_value, in_value)

    // Force the input, which we might expect to be mirrored at the output
    `DV_CHECK(uvm_hdl_force(abs_in_path, in_value))

    // Now wait 100 cycles, checking whether out_value matches the input
    repeat (100) begin
      cfg.clk_rst_vif.wait_clks(1);
      `DV_CHECK(uvm_hdl_read(abs_out_path, out_value))
      if (out_value == in_value) begin
        `DV_CHECK(is_connected)
        `DV_CHECK(uvm_hdl_release(abs_in_path))
        return;
      end
    end

    // If we got to here, the input value wasn't mirrored at the output. Check that we didn't expect
    // it to be.
    `DV_CHECK(!is_connected,
              $sformatf("Input %0s wasn't mirrored at output %0s but we thought it was connected.",
                        in_path, out_path))
    `DV_CHECK(uvm_hdl_release(abs_in_path))
  endtask

  task body();
    copy_t copies[$];
    bit    old_tl_err_pred, old_tl_error_check, old_sba_tl_check;

    `uvm_info(`gfn, $sformatf("Forcing debug enable copy: %0s", tgt_copy.name()), UVM_LOW)

    // Disable prediction of TL errors rv_dm scoreboard and TL agent. Unless Rom is enabled, TL
    // access from the debug memory will respond with d_error=1. We predict this more precisely in
    // check_fetch and check_rom.
    old_tl_err_pred = cfg.tl_err_prediction;
    old_tl_error_check = cfg.m_tl_agent_cfgs["rv_dm_mem_reg_block"].check_tl_errs;
    old_sba_tl_check = cfg.sba_tl_tx_requires_debug;
    cfg.tl_err_prediction = 1'b0;
    cfg.m_tl_agent_cfgs["rv_dm_mem_reg_block"].check_tl_errs = 0;
    cfg.sba_tl_tx_requires_debug = 1'b0;

    // The check_fetch and check_rom tasks that we will run might cause TL transactions from the ROM
    // (if tgt_copy is Rom or Fetch) but the entirety of debug is not enabled. This will cause
    // problems with the enable checker, which asserts that the debug module will not give any TL
    // responses when debug is not enabled. Disable that assertion: this sequence has a more precise
    // check anyway.
    $assertoff(0, "tb.dut.enable_checker.MemTLResponseWithoutDebugIsError_A");
    $assertoff(0, "tb.dut.enable_checker.SbaTLRequestNeedsDebug_A");

    // We are enabling a single copy by forcing a single output of a prim_lc_sync instance. This
    // causes an assertion to fail (which says that all the outputs match). Disable the assertion.
    $assertoff(0, "tb.dut.u_lc_en_sync_copies");

    // Force-enable at the given copy
    force_enable_at(tgt_copy);

    // For each copy, check whether it is enabled or not. Run through the checks in a random order.
    copies.push_back(Fetch);
    copies.push_back(Rom);
    copies.push_back(Sba);
    copies.push_back(DebugReq);
    copies.push_back(ResetReq);
    copies.shuffle();
    foreach (copies[i]) begin
      `uvm_info(`gfn, $sformatf(" Checking feature: %0s", copies[i].name()), UVM_LOW)
      check_copy(copies[i]);
    end

    // Tidy up forcing and error prediction (in case we want to run other sequences in a stress
    // sequence)
    release_enable_at(tgt_copy);
    $asserton(0, "tb.dut.u_lc_en_sync_copies");
    $asserton(0, "tb.dut.enable_checker.SbaTLRequestNeedsDebug_A");
    $asserton(0, "tb.dut.enable_checker.MemTLResponseWithoutDebugIsError_A");
    cfg.sba_tl_tx_requires_debug = old_sba_tl_check;
    cfg.m_tl_agent_cfgs["rv_dm_mem_reg_block"].check_tl_errs = old_tl_error_check;
    cfg.tl_err_prediction = old_tl_err_pred;
  endtask

endclass
