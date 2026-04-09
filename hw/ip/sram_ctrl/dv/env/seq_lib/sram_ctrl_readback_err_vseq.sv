// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// readback_err_vseq
class sram_ctrl_readback_err_vseq extends sram_ctrl_base_vseq;
  `uvm_object_utils(sram_ctrl_readback_err_vseq)

  // A tuple that describes an FI path.
  typedef struct {
    // The HDL path
    string         path;

    // All paths are relevant for write operations. If usable_for_read is true, it is also relevant
    // for read operations.
    bit            usable_for_read;

    // A mask that gives the bits that should be flipped to inject a fault
    uvm_hdl_data_t mask;
  } fi_desc_t;

  // If true, the generated memory operations will be writes. If false, they will be reads.
  rand bit m_target_write;

  // Indicates the number of memory accesses to be performed in this test.
  rand int unsigned m_num_ops;

  // Indicates at which memory access the fault is injected.
  rand int unsigned m_fi_op_idx;

  // The index of the fi_desc that should be targeted. The targeted descriptor will be copied into
  // m_targeted_desc in pre_start.
  rand int unsigned m_targeted_desc_idx;

  // The desc that is being targeted. Copied from m_fi_descs[m_targeted_desc_idx] in pre_start.
  fi_desc_t m_targeted_desc;

  local fi_desc_t m_fi_descs[$] = '{'{"sram_addr",  1'b1, 2},
                                    '{"sram_wdata", 1'b0, 2},
                                    '{"sram_we",    1'b0, 1}};

  // The readback feature raises the fatal_error alert on a mismatch.
  local string m_alert_signal = "fatal_error";

  constraint m_num_ops_c { m_num_ops == 100; }

  // Inject the fault after between 0 and m_num_ops - 20 tracked operations. The 20 operations at
  // the end give time for an alert to be raised and seen.
  constraint m_fi_op_idx_c {
    m_fi_op_idx inside {[0 : m_num_ops - 20]};
  }

  // Pick a valid desc index. If m_target_write is false, the selected descriptor must be usable for
  // reads.
  constraint valid_desc_c {
    m_targeted_desc_idx < m_fi_descs.size();
    if (!m_target_write) { m_fi_descs[m_targeted_desc_idx].usable_for_read; }
  }

  function new(string name="");
    super.new(name);
  endfunction

  // Send a single operation, that writes data to addr.
  local task do_write(bit [TL_AW-1:0] addr, bit [TL_DW-1:0] data);
    tl_access(.addr(addr), .write(1'b1), .data(data), .check_err_rsp(0), .blocking(1),
              .tl_sequencer_h(p_sequencer.tl_sequencer_hs[cfg.sram_ral_name]));
  endtask

  // Send a single operation, that reads from addr.
  local task do_read(bit [TL_AW-1:0] addr);
    bit [TL_DW-1:0] _data;
    tl_access(.addr(addr), .write(1'b0), .data(_data), .check_err_rsp(0), .blocking(1),
              .tl_sequencer_h(p_sequencer.tl_sequencer_hs[cfg.sram_ral_name]));
  endtask

  // Pick a random address to use with a read or write operation
  local function bit [TL_AW-1:0] pick_address();
    bit [TL_AW-1:0] sram_addr_mask = cfg.ral_models[cfg.sram_ral_name].get_addr_mask();
    bit [TL_AW-1:0] max_offset = {sram_addr_mask[TL_AW-1:2], 2'd0};
    bit [TL_AW-1:0] addr;

    if (!std::randomize(addr) with { (addr & sram_addr_mask) < max_offset; }) begin
      `uvm_fatal(get_name(), "Failed to randomise address.")
    end

    return addr;
  endfunction

  // Send a single random operation (either a read or a write, depending on m_target_write)
  local task send_one_req(int unsigned iteration);
    bit [TL_AW-1:0] addr = pick_address();

    if (m_target_write) begin
      do_write(addr, iteration + 1);
    end else begin
      do_read(addr);
    end
  endtask

  // Perform m_num_ops operations (either reads or writes, depending on m_target_write), returning
  // when a reset is asserted.
  //
  // If we get to the end without seeing a reset, fail with an error (because we seem not to have
  // injected the fault)
  local task send_reqs();
    for (int unsigned iteration = 0; iteration < m_num_ops; iteration++) begin
      send_one_req(iteration);

      // A reset might have been applied. If so, there's no more work to do and we can just return.
      if (!cfg.clk_rst_vif.rst_n) return;
    end

    // If we get to here, we have successfully driven the requests but haven't seen a reset. That
    // probably means the fault injector task is still counting requests, so will now wait forever.
    // Fail immediately.
    `uvm_error(get_name(), $sformatf("We drove %0d requests and never saw a reset", m_num_ops))
  endtask

  // Wait past m_fi_op_idx operations (reads or writes, depending on m_target_write) and then inject
  // a fault on the next, as described in m_targeted_desc. Finally, wait for the alert called
  // m_alert_signal to be asserted, then apply a reset.
  local task inject_fault();
    // Wait until the operation on the requested side with the given position, stopping on the
    // negedge of the clock in the middle of the operation.
    `uvm_info(get_name(),
              $sformatf("Waiting until %0s operation with index %0d",
                        m_target_write ? "write" : "read",
                        m_fi_op_idx),
              UVM_LOW)
    repeat(1 + m_fi_op_idx) begin
      cfg.fault_vif.wait_one_operation(m_target_write);
    end

    `uvm_info(get_name(),
              $sformatf("Injecting fault into %s, which should trigger the %s alert.",
                        m_targeted_desc.path, m_alert_signal),
              UVM_LOW)
    fork
      cfg.fault_vif.fault_signal(m_targeted_desc.path, m_targeted_desc.mask);
      wait_for_alert_then_reset();
    join
  endtask

  // Wait m_alert_signal is asserted, which should take at most 20 cycles, then assert a reset,
  // returning on a posedge of the main clock after it completes.
  local task wait_for_alert_then_reset();
    bit saw_reset;

    // Tell the scoreboard that we expect an alert to happen, then wait for it to be asserted.
    cfg.scb.set_exp_alert(m_alert_signal, .is_fatal(1'b1), .max_delay(20));
    wait_alert_trigger(m_alert_signal, .max_wait_cycle(20), .wait_complete(0));

    // Apply a reset
    apply_resets_concurrently();

    // Because the last reset signal to be deasserted might not have been synchronised with the main
    // clock, wait for the next posedge of that clock.
    cfg.clk_rst_vif.wait_clks(1);
  endtask

  function void post_randomize();
    super.post_randomize();

    // Copy the targeted descriptor into m_targeted_desc
    m_targeted_desc = m_fi_descs[m_targeted_desc_idx];
  endfunction

  virtual task body();
    uvm_status_e status;
    bit old_is_fi_test = cfg.is_fi_test;
    bit [2:0] old_check_tl_errs = {cfg.m_tl_agent_cfg.check_tl_errs,
                                   cfg.m_tl_agent_cfgs["sram_ctrl_regs_reg_block"].check_tl_errs,
                                   cfg.m_tl_agent_cfgs[cfg.sram_ral_name].check_tl_errs};


    // Disable some sram_ctrl checks because this is an FI test. Also, clear the check_tl_errs flag
    // for the TL agent for the memory: an injected data error might cause an integrity check to
    // fail in an unpredictable way.
    cfg.is_fi_test = 1'b1;
    cfg.m_tl_agent_cfg.check_tl_errs = 0;
    cfg.m_tl_agent_cfgs["sram_ctrl_prim_reg_block"].check_tl_errs = 0;
    cfg.m_tl_agent_cfgs[cfg.sram_ral_name].check_tl_errs = 0;

    // Request memory init & enable SRAM readback feature.
    req_mem_init();

    ral.readback.write(status, MuBi4True);
    if (status != UVM_IS_OK) begin
      `uvm_error(get_name(), "Failed to enable readback feature")
    end

    // Start the parallel threads. One will drive lots of memory requests, and the other will inject
    // a fault after a few have happened.
    fork
      send_reqs();
      inject_fault();
    join

    cfg.m_tl_agent_cfgs[cfg.sram_ral_name].check_tl_errs = old_check_tl_errs[0];
    cfg.m_tl_agent_cfgs["sram_ctrl_prim_reg_block"].check_tl_errs = old_check_tl_errs[1];
    cfg.m_tl_agent_cfg.check_tl_errs = old_check_tl_errs[2];
    cfg.is_fi_test = old_is_fi_test;
  endtask : body

endclass : sram_ctrl_readback_err_vseq
