// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
module tb;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import i3c_env_pkg::*;
  import i3c_test_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  wire clk, rst_n;
  wire clk_aon, rst_aon_n;
  wire [NUM_MAX_INTERRUPTS-1:0] interrupts;

  // I3C bus.
  wire scl, sda;
  wire cio_scl, cio_scl_en;
  wire cio_sda, cio_sda_en;
  wire ctrl_scl_pu_en, ctrl_sda_pu, ctrl_sda_pu_en;
  wire scl_hk_en, sda_hk_en;

  // interfaces
  clk_rst_if clk_rst_if(.clk(clk), .rst_n(rst_n));
  clk_rst_if clk_aon_rst_if(.clk(clk_aon), .rst_n(rst_aon_n));
  pins_if #(NUM_MAX_INTERRUPTS) intr_if(interrupts);
  tl_if tl_if(.clk(clk), .rst_n(rst_n));

  // Pull-up and high-keeper enables that the DUT drives, for observation.
  wire [NumBusCtrl-1:0] bus_ctrl;
  assign bus_ctrl[BusCtrlSdaHkEn] = sda_hk_en;
  assign bus_ctrl[BusCtrlSclHkEn] = scl_hk_en;
  assign bus_ctrl[BusCtrlSdaPuEn] = ctrl_sda_pu_en;
  assign bus_ctrl[BusCtrlSdaPu]   = ctrl_sda_pu;
  assign bus_ctrl[BusCtrlSclPuEn] = ctrl_scl_pu_en;
  pins_if #(NumBusCtrl) bus_ctrl_if(bus_ctrl);

  // Model of the I3C bus.
  // - SCL and SDA output drivers of the DUT.
  assign scl = cio_scl_en ? cio_scl : 1'bz;
  assign sda = cio_sda_en ? cio_sda : 1'bz;
  // - Pull-ups that the DUT enables during open-drain signaling.
  assign (pull0, pull1) scl = ctrl_scl_pu_en ? 1'b1 : 1'bz;
  assign (pull0, pull1) sda = ctrl_sda_pu_en ? ctrl_sda_pu : 1'bz;
  // - High-keepers that the DUT enables to hold the idle bus high.
  assign (weak0, weak1) scl = scl_hk_en ? 1'b1 : 1'bz;
  assign (weak0, weak1) sda = sda_hk_en ? 1'b1 : 1'bz;
  // - Board-level pull-ups, which the env enables only for tests that need them.
  pins_if #(.Width(NumBusLines), .PullStrength("Weak")) board_pullup_if({scl, sda});

  // Writes to the message buffer memory, which the scoreboard needs to check reads from the BUFFER
  // window.
  i3c_buf_mon_if buf_mon_if (
    .clk_i (clk),
    .rst_ni(rst_n),
    .we    (dut.u_core.u_buf.mem_req & dut.u_core.u_buf.mem_data.write),
    .sw    (dut.u_core.u_buf.idx == dut.u_core.u_buf.NumFifos),
    .addr  (dut.u_core.u_buf.mem_data.addr)
  );

  `DV_ALERT_IF_CONNECT()

  // dut
  i3c #(
    .ClkFreq      (ClkFreqMhz * 1_000_000),
    .NumTargets   (NumTargets),
    .HalfCycleScl (HalfCycleScl)
  ) dut (
    .clk_i                (clk                                   ),
    .rst_ni               (rst_n                                 ),
    .clk_aon_i            (clk_aon                               ),
    .rst_aon_ni           (rst_aon_n                             ),

    .tl_i                 (tl_if.h2d                             ),
    .tl_o                 (tl_if.d2h                             ),

    .alert_rx_i           (alert_rx                              ),
    .alert_tx_o           (alert_tx                              ),

    .racl_policies_i      (top_racl_pkg::RACL_POLICY_VEC_DEFAULT ),
    .racl_error_o         (                                      ),

    .cio_scl_i            (scl                                   ),
    .cio_scl_o            (cio_scl                               ),
    .cio_scl_en_o         (cio_scl_en                            ),
    .cio_sda_i            (sda                                   ),
    .cio_sda_o            (cio_sda                               ),
    .cio_sda_en_o         (cio_sda_en                            ),

    .ctrl_scl_pu_en_o     (ctrl_scl_pu_en                        ),
    .cio_ctrl_sda_pu_o    (ctrl_sda_pu                           ),
    .cio_ctrl_sda_pu_en_o (ctrl_sda_pu_en                        ),
    .scl_hk_en_o          (scl_hk_en                             ),
    .sda_hk_en_o          (sda_hk_en                             ),

    // There is no Target Reset detector; this matches Earl Grey.
    .rstdet_enable_o      (                                      ),
    .rstdet_o             (                                      ),
    .rstdet_i             (i3c_pkg::I3C_RSTDET_RSP_DEFAULT       ),

    .intr_hci_o           (interrupts[IntrHci]                   ),
    .intr_targ_o          (interrupts[IntrTarg]                  ),

    .ram_cfg_i            (prim_ram_1p_pkg::RAM_1P_CFG_REQ_DEFAULT),
    .ram_cfg_o            (                                      ),
    .dat_cfg_i            (prim_ram_1p_pkg::RAM_1P_CFG_REQ_DEFAULT),
    .dat_cfg_o            (                                      ),
    .dct_cfg_i            (prim_ram_1p_pkg::RAM_1P_CFG_REQ_DEFAULT),
    .dct_cfg_o            (                                      ),
    .mbist_en_i           (1'b0                                  ),
    .scan_clk_i           (1'b0                                  ),
    .scan_rst_ni          (1'b1                                  ),
    .scanmode_i           (prim_mubi_pkg::MuBi4False             )
  );

  initial begin
    // drive clk and rst_n from clk_if
    clk_rst_if.set_active();
    clk_aon_rst_if.set_active();
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_aon_rst_vif", clk_aon_rst_if);
    uvm_config_db#(intr_vif)::set(null, "*.env", "intr_vif", intr_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent*", "vif", tl_if);
    uvm_config_db#(board_pullup_vif_t)::set(null, "*.env", "board_pullup_vif", board_pullup_if);
    uvm_config_db#(bus_ctrl_vif_t)::set(null, "*.env", "bus_ctrl_vif", bus_ctrl_if);
    uvm_config_db#(virtual i3c_buf_mon_if)::set(null, "*.env", "buf_mon_vif", buf_mon_if);
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

endmodule
