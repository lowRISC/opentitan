// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
module tb;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import entropy_src_env_pkg::*;
  import entropy_src_test_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  wire clk, rst_n;
  wire devmode;
  wire efuse_es_sw_reg_en;
  wire [NUM_MAX_INTERRUPTS-1:0] interrupts;
  wire intr_entropy_valid;
  wire intr_rct_failed;
  wire intr_apt_failed;
  wire intr_fifo_err;

  // interfaces
  clk_rst_if clk_rst_if (
      .clk  (clk),
      .rst_n(rst_n)
  );
  pins_if #(NUM_MAX_INTERRUPTS) intr_if (interrupts);
  pins_if #(1) devmode_if (devmode);
  pins_if #(1) efuse_es_sw_reg_en_if (efuse_es_sw_reg_en);
  tl_if tl_if (
      .clk  (clk),
      .rst_n(rst_n)
  );

  // dut
  entropy_src dut (
      .clk_i (clk),
      .rst_ni(rst_n),

      .tl_i(tl_if.h2d),
      .tl_o(tl_if.d2h),

      .efuse_es_sw_reg_en_i(efuse_es_sw_reg_en),

      .entropy_src_hw_if_o(),
      .entropy_src_hw_if_i(),

      .entropy_src_rng_o(),
      .entropy_src_rng_i(),

      .es_entropy_valid_o(intr_entropy_valid),
      .es_rct_failed_o   (intr_rct_failed),
      .es_apt_failed_o   (intr_apt_failed),
      .es_fifo_err_o     (intr_fifo_err)
  );


  assign interrupts[EntropyValid] = intr_entropy_valid;
  assign interrupts[RctFailed] = intr_rct_failed;
  assign interrupts[AptFailed] = intr_apt_failed;
  assign interrupts[FifoErr] = intr_fifo_err;

  initial begin
    // drive clk and rst_n from clk_if
    clk_rst_if.set_active();
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(intr_vif)::set(null, "*.env", "intr_vif", intr_if);
    uvm_config_db#(devmode_vif)::set(null, "*.env", "devmode_vif", devmode_if);
    uvm_config_db#(virtual pins_if)::set(null, "*.env", "efuse_es_sw_reg_en_vif",
                                         efuse_es_sw_reg_en_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent*", "vif", tl_if);
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

endmodule
