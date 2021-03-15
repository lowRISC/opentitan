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

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  wire clk, rst_n;
  wire devmode, efuse_sw_app_enable;
  wire [NUM_MAX_INTERRUPTS-1:0] interrupts;
  wire intr_cmd_req_done;
  wire intr_entropy_req;
  wire intr_hw_inst_exc;
  wire intr_cs_fatal_err;

  // interfaces
  clk_rst_if clk_rst_if(.clk(clk), .rst_n(rst_n));
  pins_if#(NUM_MAX_INTERRUPTS) intr_if(interrupts);
  pins_if#(1) devmode_if(devmode);
  pins_if#(1) efuse_sw_app_enable_if(efuse_sw_app_enable);
  tl_if tl_if(.clk(clk), .rst_n(rst_n));
  push_pull_if#(.HostDataWidth(entropy_src_pkg::FIPS_CSRNG_BUS_WIDTH))  entropy_src_if();
  csrng_if  csrng_if(.clk(clk), .rst_n(rst_n));

  `DV_ALERT_IF_CONNECT

  // dut
  csrng#(.NHwApps(NUM_HW_APPS)) dut (
    .clk_i                   (clk      ),
    .rst_ni                  (rst_n    ),

    .tl_i                    (tl_if.h2d),
    .tl_o                    (tl_if.d2h),

    .efuse_sw_app_enable_i   (efuse_sw_app_enable),

    // TODO: Use parameter?
    .lc_hw_debug_en_i        (4'b1010),

    .entropy_src_hw_if_o     (entropy_src_if.req),
    .entropy_src_hw_if_i     ({entropy_src_if.ack, entropy_src_if.h_data[entropy_src_pkg::
                               CSRNG_BUS_WIDTH-1:0], entropy_src_if.h_data[entropy_src_pkg::
                               CSRNG_BUS_WIDTH]}),

    .csrng_cmd_i             (csrng_if.cmd_req),
    .csrng_cmd_o             (csrng_if.cmd_rsp),

    .alert_rx_i              (alert_rx),
    .alert_tx_o              (alert_tx),

    .intr_cs_cmd_req_done_o  (intr_cmd_req_done),
    .intr_cs_entropy_req_o   (intr_entropy_req),
    .intr_cs_hw_inst_exc_o   (intr_hw_inst_exc),
    .intr_cs_fatal_err_o     (intr_cs_fatal_err)
  );

  assign interrupts[CmdReqDone] = intr_cmd_req_done;
  assign interrupts[EntropyReq] = intr_entropy_req;
  assign interrupts[HwInstExc]  = intr_hw_inst_exc;
  assign interrupts[FifoErr]    = intr_cs_fatal_err;

  initial begin
    // drive clk and rst_n from clk_if
    clk_rst_if.set_active();
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(intr_vif)::set(null, "*.env", "intr_vif", intr_if);
    uvm_config_db#(devmode_vif)::set(null, "*.env", "devmode_vif", devmode_if);
    uvm_config_db#(virtual pins_if)::set(null, "*.env", "efuse_sw_app_enable_vif",
                                         efuse_sw_app_enable_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent*", "vif", tl_if);
    uvm_config_db#(virtual push_pull_if#(.HostDataWidth(entropy_src_pkg::FIPS_CSRNG_BUS_WIDTH)))::set
                                        (null, "*.env.m_entropy_src_agent*", "vif", entropy_src_if);
    uvm_config_db#(virtual csrng_if)::set(null, "*.env.m_csrng_agent*", "vif", csrng_if);
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

endmodule
