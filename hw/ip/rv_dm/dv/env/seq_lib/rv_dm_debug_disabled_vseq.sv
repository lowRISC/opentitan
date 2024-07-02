// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rv_dm_debug_disabled_vseq extends rv_dm_base_vseq;
  `uvm_object_utils(rv_dm_debug_disabled_vseq)
  `uvm_object_new

  // Override the constraint in rv_dm_base_vseq that enables debug (to disable it instead)
  constraint debug_enabled_c {
    lc_hw_debug_en == 1'b0;
  }

  // Check that the "mem" TL interface is disabled as expected
  task check_no_mem_if();
    // Try to do an arbitrary TL access to the interface. We don't expect it to work, which is
    // checked in the scoreboard (in predict_tl_err).
    csr_wr(.ptr(tl_mem_ral.halted), .value(0));
  endtask

  // Check that some signal that comes out of dm_top doesn't make it as far as the rv_dm toplevel
  task check_no_dm_output(string         dm_top_port,
                          string         rv_dm_port,
                          uvm_reg_data_t forced_input,
                          uvm_reg_data_t expected_output);
    string in_path = {"tb.dut.u_dm_top.", dm_top_port};
    string out_path = {"tb.dut.", rv_dm_port};

    `DV_CHECK(uvm_hdl_force(in_path, forced_input))
    repeat (100) begin
      uvm_reg_data_t rvalue;
      `DV_CHECK(uvm_hdl_read(out_path, rvalue));
      `DV_CHECK(rvalue == expected_output)
      cfg.clk_rst_vif.wait_clks(1);
    end
    `DV_CHECK(uvm_hdl_release(in_path))
  endtask

  // Check that an ndmreset signal can't come out of rv_dm.
  task check_no_ndmreset();
    check_no_dm_output("ndmreset_o", "ndmreset_req_o", 1'b1, 1'b0);
  endtask

  // Check that a debug_req signal can't come out of rv_dm.
  task check_no_debug_req();
    check_no_dm_output("debug_req_o", "debug_req_o", 1'b1, 1'b0);
  endtask


  task body();
    // Disable TL error checks in tl_reg_adapter. It doesn't expect to see TL errors (since it's not
    // doing anything untoward), but we've configured rv_dm to respond with an error to *every*
    // request.
    cfg.m_tl_agent_cfgs["rv_dm_mem_reg_block"].check_tl_errs = 0;

    repeat (4) begin
      // Pick an arbitrary value for lc_hw_debug_en_i other than On and then wait a short time to
      // make sure it has had an effect.
      upd_lc_hw_debug_en();
      `uvm_info(`gfn,
                $sformatf("Setting lc_hw_debug_en to %0x", cfg.rv_dm_vif.lc_hw_debug_en),
                UVM_LOW)
      cfg.clk_rst_vif.wait_clks(10);

      randcase
        1: check_no_mem_if();
        1: check_no_ndmreset();
        1: check_no_debug_req();
      endcase
    end
  endtask

endclass
