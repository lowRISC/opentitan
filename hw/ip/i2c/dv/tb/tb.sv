// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
module tb;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import i2c_env_pkg::*;
  import i2c_test_pkg::*;
  import top_racl_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  wire clk, rst_n;
  wire intr_fmt_threshold;
  wire intr_rx_threshold;
  wire intr_acq_threshold;
  wire intr_rx_overflow;
  wire intr_controller_halt;
  wire intr_scl_interference;
  wire intr_sda_interference;
  wire intr_stretch_timeout;
  wire intr_sda_unstable;
  wire intr_cmd_complete;
  wire intr_tx_stretch;
  wire intr_tx_threshold;
  wire intr_acq_stretch;
  wire intr_unexp_stop;
  wire intr_host_timeout;
  wire [NUM_MAX_INTERRUPTS-1:0] interrupts;

  wire cio_scl;
  wire cio_sda;
  wire cio_scl_en;
  wire cio_sda_en;

  racl_policy_vec_t racl_policies;
  assign racl_policies = 0; // Not currently used

  // interfaces
  clk_rst_if clk_rst_if(.clk(clk), .rst_n(rst_n));
  pins_if #(NUM_MAX_INTERRUPTS) intr_if(interrupts);

  tl_if tl_if(.clk(clk), .rst_n(rst_n));

  wire scl, sda;
  i2c_if i2c_if(
    .clk_i(clk),
    .rst_ni(rst_n),
    .scl_io(scl),
    .sda_io(sda)
  );

  // TODO: Remove this unused interface.
  i2c_dv_if i2c_dv_if(
    .clk(clk),
    .rst_n(rst_n)
  );

  `ifndef I2C_HIER
    `define I2C_HIER tb.dut.i2c_core
  `endif

  // Model PAD behavior
  i2c_port_conv i2c_port_conv (
    .scl_oe_i(cio_scl_en),
    .sda_oe_i(cio_sda_en),
    .scl_o(cio_scl),
    .sda_o(cio_sda),
    .scl_io(scl),
    .sda_io(sda)
  );

  // Model external pull-up resistor
  assign (weak0, weak1) scl = 1'b1;
  assign (weak0, weak1) sda = 1'b1;

  // clk and rst_n is used for alert_if in `DV_ALERT_IF_CONNECT
  `DV_ALERT_IF_CONNECT()

  // dut
  i2c dut (
    .clk_i                   (clk        ),
    .rst_ni                  (rst_n      ),
    .ram_cfg_i               (prim_ram_1p_pkg::RAM_1P_CFG_DEFAULT),
    .ram_cfg_rsp_o           (                                   ),

    .tl_i                    (tl_if.h2d  ),
    .tl_o                    (tl_if.d2h  ),

    .alert_rx_i              (alert_rx   ),
    .alert_tx_o              (alert_tx   ),

    .racl_policies_i         (racl_policies),
    .racl_error_o            (             ),

    .cio_scl_i               (cio_scl               ),
    .cio_scl_o               (/*hardcoded to 0*/    ),
    .cio_scl_en_o            (cio_scl_en            ),
    .cio_sda_i               (cio_sda               ),
    .cio_sda_o               (/*hardcoded to 0*/    ),
    .cio_sda_en_o            (cio_sda_en            ),
    .lsio_trigger_o          (                      ),

    .intr_fmt_threshold_o    (intr_fmt_threshold    ),
    .intr_rx_threshold_o     (intr_rx_threshold     ),
    .intr_acq_threshold_o    (intr_acq_threshold    ),
    .intr_rx_overflow_o      (intr_rx_overflow      ),
    .intr_controller_halt_o  (intr_controller_halt  ),
    .intr_scl_interference_o (intr_scl_interference ),
    .intr_sda_interference_o (intr_sda_interference ),
    .intr_stretch_timeout_o  (intr_stretch_timeout  ),
    .intr_sda_unstable_o     (intr_sda_unstable     ),
    .intr_cmd_complete_o     (intr_cmd_complete     ),
    .intr_tx_stretch_o       (intr_tx_stretch       ),
    .intr_tx_threshold_o     (intr_tx_threshold     ),
    .intr_acq_stretch_o      (intr_acq_stretch      ),
    .intr_unexp_stop_o       (intr_unexp_stop       ),
    .intr_host_timeout_o     (intr_host_timeout     )
  );

  // interrupt
  assign interrupts[FmtThreshold]   = intr_fmt_threshold;
  assign interrupts[RxThreshold]    = intr_rx_threshold;
  assign interrupts[AcqThreshold]   = intr_acq_threshold;
  assign interrupts[RxOverflow]     = intr_rx_overflow;
  assign interrupts[ControllerHalt] = intr_controller_halt;
  assign interrupts[SclInference]   = intr_scl_interference;
  assign interrupts[SdaInference]   = intr_sda_interference;
  assign interrupts[StretchTimeout] = intr_stretch_timeout;
  assign interrupts[SdaUnstable]    = intr_sda_unstable;
  assign interrupts[CmdComplete]    = intr_cmd_complete;
  assign interrupts[TxStretch]      = intr_tx_stretch;
  assign interrupts[TxThreshold]    = intr_tx_threshold;
  assign interrupts[AcqStretch]     = intr_acq_stretch;
  assign interrupts[UnexpStop]      = intr_unexp_stop;
  assign interrupts[HostTimeout]    = intr_host_timeout;

  initial begin
    // drive clk and rst_n from clk_if
    clk_rst_if.set_active();
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(intr_vif)::set(null, "*.env", "intr_vif", intr_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent*", "vif", tl_if);
    uvm_config_db#(virtual i2c_if)::set(null, "*.env.m_i2c_agent*", "vif", i2c_if);
    uvm_config_db#(virtual i2c_dv_if)::set(null, "*.env", "i2c_dv_vif", i2c_dv_if);
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end
endmodule : tb
