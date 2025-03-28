// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// smoke test vseq
class rv_dm_smoke_vseq extends rv_dm_base_vseq;
  `uvm_object_utils(rv_dm_smoke_vseq)
  `uvm_object_new

  // Check that the IDCODE register works as expected.
  //
  // Write an arbitrary value to the register, which should be ignored because this is a read-only
  // register. Then read the value back. We expect to see RV_DM_JTAG_IDCODE, which the testbench has
  // passed to the DUT as the IdcodeValue parameter.
  task check_idcode();
    uvm_reg_data_t data;
    `DV_CHECK_STD_RANDOMIZE_FATAL(data)
    csr_wr(.ptr(jtag_dtm_ral.idcode), .value(data));
    csr_rd(.ptr(jtag_dtm_ral.idcode), .value(data));
    if (cfg.clk_rst_vif.rst_n) `DV_CHECK_EQ(data, RV_DM_JTAG_IDCODE)
  endtask

  // Check that writing to haltreq controls the debug_req_o output.
  //
  // The haltreq bit is supposed to tell the (only) hart to halt and allow debug. This is
  // implemented in OpenTitan with a debug_req_o signal coming out of rv_dm. Check that it's wired
  // up correctly.
  task check_haltreq();
    uvm_reg_data_t data = $urandom_range(0, 1);
    csr_wr(.ptr(jtag_dmi_ral.dmcontrol.haltreq), .value(data));

    // Check immediately that the write has been reflected in the debug_req_o output. There's no
    // need to wait because the write goes through a jtag_dmi_agent, which follows the write
    // operation with a read operation (polling) to check that it was applied.
    if (cfg.clk_rst_vif.rst_n) `DV_CHECK_EQ(cfg.rv_dm_vif.cb.debug_req, data)
  endtask

  // Check that the ndmreset field controls the ndmreset_req_o output
  //
  // This is analogous to check_haltreq. Here, we expect the ndmreset field in the dmcontrol
  // register to control the ndmreset_req_o output signal.
  task check_ndmreset();
    uvm_reg_data_t data = $urandom_range(0, 1);
    csr_wr(.ptr(jtag_dmi_ral.dmcontrol.ndmreset), .value(data));
    if (cfg.clk_rst_vif.rst_n) `DV_CHECK_EQ(cfg.rv_dm_vif.cb.ndmreset_req, data)
  endtask

  // Verify that the dmstatus[*unavail] field tracks the unavailable_i input.
  task check_unavailable();
    uvm_reg_data_t data = $urandom_range(0, 1);
    cfg.rv_dm_vif.cb.unavailable <= data;
    csr_rd(.ptr(jtag_dmi_ral.dmstatus), .value(data));
    if (cfg.clk_rst_vif.rst_n) begin
      `DV_CHECK_EQ(cfg.rv_dm_vif.unavailable,
                   get_field_val(jtag_dmi_ral.dmstatus.anyunavail, data))
      `DV_CHECK_EQ(cfg.rv_dm_vif.unavailable,
                   get_field_val(jtag_dmi_ral.dmstatus.allunavail, data))
    end
  endtask

  // Send an TL access with an integrity error, checking that it causes a fatal alert. Because the
  // alert is fatal, we have to finish by issuing a reset to tidy up after ourselves. This allows a
  // subsequent item to run (and means we don't have to set expect_fatal_alerts from cip_base_vseq).
  task check_tl_integrity_error();
    // Pick a random RAL model to operate on
    int ral_model_idx = $urandom_range(0, cfg.ral_model_names.size()-1);
    string ral_model_name = cfg.ral_model_names[ral_model_idx];

    // This task will finish by applying a reset. If do_apply_reset is false, we're probably running
    // inside stress_all_with_rand_reset and applying a reset ourselves will confuse things. Fail
    // instantly to make this easier to debug.
    `DV_CHECK_FATAL(do_apply_reset)

    // Disable TL assertions while we send the bad access (one will definitely fail)
    set_tl_assert_en(.enable(0));

    // Issue a TL access on the selected RAL that contains an integrity error
    issue_tl_access_w_intg_err(ral_model_name);

    // Check that a fatal alert comes out
    check_tl_intg_error_response();

    // Clean up after ourselves
    dut_init("HARD");
    set_tl_assert_en(.enable(1));
  endtask

  // Verify that writing to dmactive causes dmactive output to be set.
  //
  // If a reset is asserted somewhere in the middle, the DMI write to dmcontrol will have been
  // ignored. Skip the check and write 1 to seen_reset.
  task check_dmactive(output bit seen_reset);
    uvm_reg_data_t data = $urandom_range(0, 1);

    fork begin : isolation_fork
      fork
        begin
          wait (!cfg.clk_rst_vif.rst_n);
          seen_reset = 1'b1;
        end
        begin
          csr_wr(.ptr(jtag_dmi_ral.dmcontrol.dmactive), .value(data));

          // Wait for the DMI transaction to make it from the JTAG clock domain to the system clock.
          // This goes through a dmi_cdc module and takes two JTAG clock cycles.
          cfg.m_jtag_agent_cfg.vif.wait_tck(2);
        end
      join_any
      if (!seen_reset) disable fork;
    end join

    if (!seen_reset) begin
      `DV_CHECK_EQ(cfg.rv_dm_vif.cb.dmactive, data)
    end
  endtask

  task body();
    bit should_stop = 1'b0;

    repeat ($urandom_range(20, 50)) begin
      randcase
        10: check_idcode();
        10: check_haltreq();
        10: check_ndmreset();
        10: check_unavailable();
        do_apply_reset * 1: check_tl_integrity_error();
      endcase

      spot_resets(should_stop);
      if (should_stop) return;

      cfg.clk_rst_vif.wait_clks($urandom_range(1, 10));
    end

    repeat ($urandom_range(1, 5)) begin
      check_dmactive(should_stop);
      spot_resets(should_stop);

      if (should_stop) return;

      cfg.clk_rst_vif.wait_clks($urandom_range(1, 10));
    end

    // Tidy up by making sure that ndmreset isn't currently being asserted (to avoid confusion in
    // any sequence that follows us in a stress_all test)
    csr_wr(.ptr(jtag_dmi_ral.dmcontrol.ndmreset), .value(0));
  endtask : body

endclass : rv_dm_smoke_vseq
