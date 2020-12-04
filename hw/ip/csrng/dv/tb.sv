// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
module tb;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import csrng_env_pkg::*;
  import csrng_test_pkg::*;
  import entropy_src_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  wire clk, rst_n;
  wire devmode, fips, efuse_sw_app_enable;
  wire [NUM_MAX_INTERRUPTS-1:0] interrupts;
  wire intr_cmd_req_done;
  wire intr_entropy_req;
  wire intr_hw_inst_exc;
  wire intr_fifo_err;

  // interfaces
  clk_rst_if clk_rst_if(.clk(clk), .rst_n(rst_n));
  pins_if#(NUM_MAX_INTERRUPTS) intr_if(interrupts);
  pins_if#(1) devmode_if(devmode);
  pins_if#(1) fips_if(fips);
  pins_if#(1) efuse_sw_app_enable_if(efuse_sw_app_enable);
  tl_if tl_if(.clk(clk), .rst_n(rst_n));
  push_pull_if#(.HostDataWidth(CSRNG_DATA_WIDTH)) entropy_src_if();

  // dut
  csrng#(.NumHwApps(NUMHWAPPS)) dut (
    .clk_i                   (clk      ),
    .rst_ni                  (rst_n    ),

    .tl_i                    (tl_if.h2d),
    .tl_o                    (tl_if.d2h),

    .efuse_sw_app_enable_i   (efuse_sw_app_enable),

    // TODO: Use parameter?
    .lc_dft_en_i             (4'b1010),

    .entropy_src_hw_if_o     (entropy_src_if.req),
    // TODO: fips input hardcoded to 1'b0 for now
    .entropy_src_hw_if_i     ({entropy_src_if.ack, entropy_src_if.data, 1'b0}),

    .csrng_cmd_i             ('h0),
    .csrng_cmd_o             (   ),

    .intr_cs_cmd_req_done_o  (intr_cmd_req_done),
    .intr_cs_entropy_req_o   (intr_entropy_req),
    .intr_cs_hw_inst_exc_o   (intr_hw_inst_exc),
    .intr_cs_fifo_err_o      (intr_fifo_err)
  );

  assign interrupts[CmdReqDone] = intr_cmd_req_done;
  assign interrupts[EntropyReq] = intr_entropy_req;
  assign interrupts[HwInstExc]  = intr_hw_inst_exc;
  assign interrupts[FifoErr]    = intr_fifo_err;

  initial begin
    // drive clk and rst_n from clk_if
    clk_rst_if.set_active();
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(intr_vif)::set(null, "*.env", "intr_vif", intr_if);
    uvm_config_db#(devmode_vif)::set(null, "*.env", "devmode_vif", devmode_if);
    uvm_config_db#(virtual pins_if)::set(null, "*.env", "fips_vif", fips_if);
    uvm_config_db#(virtual pins_if)::set(null, "*.env", "efuse_sw_app_enable_vif",
                                         efuse_sw_app_enable_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent*", "vif", tl_if);
    uvm_config_db#(virtual push_pull_if#(.HostDataWidth(CSRNG_DATA_WIDTH)))::set(null,
                   "*.env.m_entropy_src_agent*", "vif", entropy_src_if);
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

endmodule
