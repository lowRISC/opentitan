// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rv_dm_jtag_dmi_debug_disabled_vseq extends rv_dm_base_vseq;
  `uvm_object_utils(rv_dm_jtag_dmi_debug_disabled_vseq)
  `uvm_object_new

  // Override the constraint in rv_dm_base_vseq that enables debug (to disable it instead)
  constraint debug_enabled_c {
    lc_hw_debug_en == 1'b0;
  }

  task automatic write_abstractdata(uvm_reg_data_t value);
    csr_wr(.ptr(jtag_dmi_ral.abstractdata[0]), .value(value));
  endtask

  task automatic read_abstractdata(uvm_reg_data_t expected_value);
    uvm_reg_data_t rdata;
    csr_rd(.ptr(jtag_dmi_ral.abstractdata[0]), .value(rdata));
    `DV_CHECK_EQ(rdata, expected_value);
  endtask

  // Possibly wait a short time.
  //
  // The probability of a zero wait is intentionally reasonably large, because this is likely to be
  // the timing that's most likely to trigger errors.
  task maybe_delay();
    if ($urandom_range(1, 0)) begin
      cfg.clk_rst_vif.wait_clks($urandom_range(20, 1));
    end
  endtask

  task body();
    repeat ($urandom_range(1, 10)) begin
      bit [31:0] value0, value1;
      `DV_CHECK_STD_RANDOMIZE_FATAL(value0)
      `DV_CHECK_STD_RANDOMIZE_FATAL(value1)

      // Write value0 to abstractdata[0], then read it back, checking the value has arrived as
      // expected.
      write_abstractdata(value0);
      read_abstractdata(value0);

      // Possibly wait a bit
      maybe_delay();

      // Pick an arbitrary value for lc_hw_debug_en_i other than On
      upd_lc_hw_debug_en();

      // Wait a few cycles to make sure that the changed enable signal has made it through a
      // prim_lc_sync. If we start the next operation too early, things will get rather confused
      // because only the latter half of a JTAG operation will get through.
      cfg.clk_rst_vif.wait_clks(3);

      // Write a different value to abstractdata[0] than read it back. The write should be ignored
      // and the register should read as its reset value (because the debug block is disabled).
      write_abstractdata(value1);
      read_abstractdata(jtag_dmi_ral.abstractdata[0].get_reset());

      // Possibly wait a bit
      maybe_delay();

      // Issue a JTAG reset through trst_n and switch lc_hw_debug_en to On.
      cfg.m_jtag_agent_cfg.vif.do_trst_n(2);
      cfg.rv_dm_vif.cb.pinmux_hw_debug_en <= lc_ctrl_pkg::On;

      // Wait again to make sure the LC signal makes it through the prim_lc_sync
      cfg.clk_rst_vif.wait_clks(3);

      // Read the contents of abstractdata[0] and check they are what we set at the start.
      read_abstractdata(value0);
    end
  endtask : body

endclass  : rv_dm_jtag_dmi_debug_disabled_vseq
