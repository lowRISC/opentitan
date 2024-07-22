// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rv_dm_jtag_dmi_debug_disabled_vseq extends rv_dm_base_vseq;
  `uvm_object_utils(rv_dm_jtag_dmi_debug_disabled_vseq)
  `uvm_object_new

  task automatic write_abstractdata(uvm_reg_data_t value);
    csr_wr(.ptr(jtag_dmi_ral.abstractdata[0]), .value(value));
  endtask

  task automatic read_abstractdata(uvm_reg_data_t expected_value);
    uvm_reg_data_t rdata;
    csr_rd(.ptr(jtag_dmi_ral.abstractdata[0]), .value(rdata));
    if (cfg.clk_rst_vif.rst_n) `DV_CHECK_EQ(rdata, expected_value);
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

  // Control the pinmux_hw_debug_en_i signal, waiting long enough to ensure the signal has
  // synchronised properly.
  task control_pinmux_enable(bit enable);
    pinmux_hw_debug_en = enable;
    upd_pinmux_hw_debug_en();

    // Wait a few cycles to make sure that the changed pinmux signal has made it through a
    // prim_lc_sync. If we start the next operation too early, things will get rather confused
    // because only half of a JTAG operation will get through.
    cfg.clk_rst_vif.wait_clks(3);
  endtask

  task body();
    bit [31:0] value0, value1;
    `DV_CHECK_STD_RANDOMIZE_FATAL(value0)
    `DV_CHECK_STD_RANDOMIZE_FATAL(value1)

    // At the start of the vseq, we expect that pinmux_hw_debug_en_i is On, so we should have a
    // working DMI connection. Write some arbitrary value to abstractdata 0.
    write_abstractdata(value0);
    read_abstractdata(value0);
    if (!cfg.clk_rst_vif.rst_n) return;

    // Possibly wait a bit
    maybe_delay();

    // Now we want to disable the DMI connection by setting pinmux_hw_debug_en_i to a value other
    // than On.
    control_pinmux_enable(1'b0);

    // Write a different value to abstractdata[0] than read it back. The write should be ignored
    // and the register should read as zero (because the JTAG connection isn't actually up).
    write_abstractdata(value1);
    read_abstractdata(0);
    if (!cfg.clk_rst_vif.rst_n) return;

    // Possibly wait a bit
    maybe_delay();

    // Issue a JTAG reset through trst_n and reconnect the DMI
    cfg.m_jtag_agent_cfg.vif.do_trst_n(2);
    control_pinmux_enable(1'b1);

    // Read the contents of abstractdata[0] and check they are what we set at the start.
    read_abstractdata(value0);
  endtask : body

endclass  : rv_dm_jtag_dmi_debug_disabled_vseq
