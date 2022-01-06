// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

module tb;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import spi_host_env_pkg::*;
  import spi_host_test_pkg::*;
  import spi_host_reg_pkg::*;
  import lc_ctrl_pkg::*;

  import spi_device_pkg::passthrough_req_t;
  import spi_device_pkg::passthrough_rsp_t;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  wire clk, rst_n;
  wire                          devmode;
  wire [NUM_MAX_INTERRUPTS-1:0] interrupts;
  wire [3:0]                    si_pulldown;
  wire [3:0]                    so_pulldown;

  lc_tx_t                       scanmode_i;
  logic                         cio_sck_o;
  logic                         cio_sck_en_o;
  logic [NumCS-1:0]             cio_csb_o;
  logic [NumCS-1:0]             cio_csb_en_o;
  logic [3:0]                   cio_sd_o;
  logic [3:0]                   cio_sd_en_o;
  logic [3:0]                   cio_sd_i;
  logic                         intr_error;
  logic                         intr_event;

  passthrough_req_t             passthrough_i;
  passthrough_rsp_t             passthrough_o;

  // interfaces
  clk_rst_if   clk_rst_if(.clk(clk), .rst_n(rst_n));
  pins_if #(1) devmode_if(devmode);
  pins_if #(NUM_MAX_INTERRUPTS) intr_if(.pins(interrupts));
  tl_if        tl_if(.clk(clk), .rst_n(rst_n));
  spi_if       spi_if(.rst_n(rst_n));

  `DV_ALERT_IF_CONNECT

  // dut
  spi_host dut (
    .clk_i                (clk),
    .rst_ni               (rst_n),

    // tl i/f
    .tl_i                 (tl_if.h2d),
    .tl_o                 (tl_if.d2h),
    // alerts
    .alert_rx_i           (alert_rx),
    .alert_tx_o           (alert_tx),
    // spi i/o
    .cio_sck_o            (cio_sck_o),
    .cio_sck_en_o         (cio_sck_en_o),
    .cio_csb_o            (cio_csb_o),
    .cio_csb_en_o         (cio_csb_en_o),
    .cio_sd_o             (cio_sd_o),
    .cio_sd_en_o          (cio_sd_en_o),
    .cio_sd_i             (si_pulldown),
    // passthrough i/o
    .passthrough_i        (passthrough_i),
    .passthrough_o        (passthrough_o),
    // intr i/f
    .intr_error_o         (intr_error),
    .intr_spi_event_o     (intr_event)
  );

  // configure passthrough i/o
  assign passthrough_i.sck = clk;
  // TODO - V2 connect passtrhough to another agent
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      passthrough_i.passthrough_en <= 1'b0;
      passthrough_i.sck_en <= 1'b0;
      passthrough_i.csb_en <= 1'b0;
      passthrough_i.s_en   <= 1'b0;
      passthrough_i.sck_gate_en <= 1'b0;
      passthrough_i.csb    <= 1'b1;
      passthrough_i.s      <= '0;
    end else begin
      passthrough_i.passthrough_en <= 1'b0;
      passthrough_i.sck_en <= 1'b1;
      passthrough_i.csb_en <= 1'b1;
      passthrough_i.s_en   <= 1'b1;
      passthrough_i.csb    <= 1'b0;
      passthrough_i.s      <= ~passthrough_i.s;
    end
  end




  // configure spi_if i/o
  assign spi_if.sck = (cio_sck_en_o) ? cio_sck_o : 1'bz;
  for (genvar i = 0; i < 4; i++) begin : gen_tri_state
    pullup (weak1) pd_in_i (si_pulldown[i]);
    pullup (weak1) pd_out_i (so_pulldown[i]);
    assign spi_if.sio[i]  = (cio_sd_en_o[i]) ? cio_sd_o[i] : so_pulldown[i];
    assign si_pulldown[i] = spi_if.sio[i];

    assign spi_if.csb[i] = (i < NumCS && cio_csb_en_o[i]) ? cio_csb_o[i] : 1'b1;
  end

  assign interrupts[SpiHostError] = intr_error;
  assign interrupts[SpiHostEvent] = intr_event;

  initial begin
    // drive clk and rst_n from clk_if
    clk_rst_if.set_active();
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(intr_vif)::set(null, "*.env", "intr_vif", intr_if);
    uvm_config_db#(devmode_vif)::set(null, "*.env", "devmode_vif", devmode_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent*", "vif", tl_if);
    uvm_config_db#(virtual spi_if)::set(null, "*.env.m_spi_agent*", "vif", spi_if);
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

endmodule
