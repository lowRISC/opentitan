// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
module tb;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import entropy_src_pkg::*;
  import entropy_src_env_pkg::*;
  import entropy_src_test_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  wire clk, rst_n;
  wire devmode, fips, efuse_es_sw_reg_en;
  wire [NUM_MAX_INTERRUPTS-1:0] interrupts;
  prim_alert_pkg::alert_rx_t [NUM_ALERTS-1:0] alert_rx;
  prim_alert_pkg::alert_tx_t [NUM_ALERTS-1:0] alert_tx;
  wire intr_entropy_valid;
  wire intr_health_test_failed;
  wire intr_fifo_err;

  // interfaces
  clk_rst_if clk_rst_if(.clk(clk), .rst_n(rst_n));
  pins_if#(NUM_MAX_INTERRUPTS) intr_if(interrupts);
  alert_esc_if alert_if[NUM_ALERTS](.clk(clk), .rst_n(rst_n));
  pins_if#(1) devmode_if(devmode);
  pins_if#(1) fips_if(fips);
  pins_if#(1) efuse_es_sw_reg_en_if(efuse_es_sw_reg_en);
  tl_if tl_if(.clk(clk), .rst_n(rst_n));
  push_pull_if#(.DataWidth(RNG_DATA_WIDTH)) rng_if(.clk(clk), .rst_n(rst_n));
  push_pull_if#(.DataWidth(CSRNG_DATA_WIDTH)) csrng_if(.clk(clk), .rst_n(rst_n));

  // dut
  entropy_src dut (
    .clk_i                     (clk        ),
    .rst_ni                    (rst_n      ),

    .tl_i                      (tl_if.h2d  ),
    .tl_o                      (tl_if.d2h  ),

    .efuse_es_sw_reg_en_i      (efuse_es_sw_reg_en),

    .entropy_src_hw_if_o       ({csrng_if.ack, csrng_if.data, fips}),
    .entropy_src_hw_if_i       (csrng_if.req),

    .entropy_src_rng_o         (rng_if.ready),
    .entropy_src_rng_i         ({rng_if.valid, rng_if.data}),

    .alert_rx_i                (alert_rx),
    .alert_tx_o                (alert_tx),

    .es_entropy_valid_o        (intr_entropy_valid),
    .es_health_test_failed_o   (intr_health_test_failed),
    .es_fifo_err_o             (intr_fifo_err)
  );

  assign interrupts[EntropyValid]     = intr_entropy_valid;
  assign interrupts[HealthTestFailed] = intr_health_test_failed;
  assign interrupts[FifoErr]          = intr_fifo_err;

  for (genvar k = 0; k < NUM_ALERTS; k++) begin : connect_alerts_pins
    assign alert_rx[k] = alert_if[k].alert_rx;
    assign alert_if[k].alert_tx = alert_tx[k];
    initial begin
      uvm_config_db#(virtual alert_esc_if)::set(null, $sformatf("*.env.m_alert_agent_%0s",
          LIST_OF_ALERTS[k]), "vif", alert_if[k]);
    end
  end

  initial begin
    // drive clk and rst_n from clk_if
    //Set interfaces in config_db
    clk_rst_if.set_active();
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(intr_vif)::set(null, "*.env", "intr_vif", intr_if);
    uvm_config_db#(devmode_vif)::set(null, "*.env", "devmode_vif", devmode_if);
    uvm_config_db#(virtual pins_if)::set(null, "*.env", "efuse_es_sw_reg_en_vif", efuse_es_sw_reg_en_if);
    uvm_config_db#(virtual pins_if)::set(null, "*.env", "fips_vif", fips_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent*", "vif", tl_if);
    uvm_config_db#(virtual push_pull_if#(.DataWidth(RNG_DATA_WIDTH)))::set(null, "*.env.m_rng_agent*", "vif", rng_if);
    uvm_config_db#(virtual push_pull_if#(.DataWidth(CSRNG_DATA_WIDTH)))::set(null, "*.env.m_csrng_agent*", "vif", csrng_if);
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

endmodule
