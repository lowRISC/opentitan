// Copyright lowRISC contributors (OpenTitan project).
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
  wire [NUM_MAX_INTERRUPTS-1:0] interrupts;
  wire [3:0]                    si_pulldown;
  wire [3:0]                    so_pulldown;
  wire [3:0]                    sio;

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
  pins_if #(NUM_MAX_INTERRUPTS) intr_if(.pins(interrupts));
  tl_if        tl_if(.clk(clk), .rst_n(rst_n));
  spi_if       spi_if(.rst_n(rst_n), .sio(sio));
  spi_passthrough_if       spi_passthrough_if(.rst_n(rst_n));

  `DV_ALERT_IF_CONNECT()

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
    .cio_sd_i             (cio_sd_i),
    // passthrough i/o
    .passthrough_i        (passthrough_i),
    .passthrough_o        (passthrough_o),
    // intr i/f
    .intr_error_o         (intr_error),
    .intr_spi_event_o     (intr_event)
  );

  assign passthrough_i.passthrough_en = spi_passthrough_if.passthrough_en;
  assign passthrough_i.sck_en         = spi_passthrough_if.sck_en;
  assign passthrough_i.csb_en         = spi_passthrough_if.csb_en;
  assign passthrough_i.s_en           = spi_passthrough_if.s_en;
  assign passthrough_i.csb            = spi_passthrough_if.csb;
  assign passthrough_i.sck            = spi_passthrough_if.sck;

  assign passthrough_i.s                 = spi_passthrough_if.is;
  assign spi_passthrough_if.os           = passthrough_o.s;
  assign spi_passthrough_if.cio_sck_o    = cio_sck_o;
  assign spi_passthrough_if.cio_sck_en_o = cio_sck_en_o;
  assign spi_passthrough_if.cio_csb_o    = cio_csb_o;
  assign spi_passthrough_if.cio_csb_en_o = cio_csb_en_o;
  assign spi_passthrough_if.cio_sd_en_o  = cio_sd_en_o;
  assign spi_passthrough_if.cio_sd_o     = cio_sd_o;

  assign cio_sd_i = spi_passthrough_if.passthrough_en ? spi_passthrough_if.cio_sd_i : si_pulldown;

  // configure spi_if i/o
  assign spi_if.sck = (cio_sck_en_o) ? cio_sck_o : 1'bz;
  for (genvar i = 0; i < 4; i++) begin : gen_tri_state
    pullup (weak1) pd_in_i (si_pulldown[i]);
    pullup (weak1) pd_out_i (so_pulldown[i]);
    assign sio[i]  = (cio_sd_en_o[i]) ? cio_sd_o[i] : 'z;
    assign (highz0, pull1) sio[i] = !cio_sd_en_o[i];
    assign si_pulldown[i] = sio[i];

    if (i < NumCS) begin : gen_drive_csb
      assign spi_if.csb[i] = cio_csb_en_o[i] ? cio_csb_o[i] : 1'b1;
    end
  end

  assign interrupts[SpiHostError] = intr_error;
  assign interrupts[SpiHostEvent] = intr_event;

  initial begin
    // drive clk and rst_n from clk_if
    clk_rst_if.set_active();
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(intr_vif)::set(null, "*.env", "intr_vif", intr_if);
    uvm_config_db#(virtual spi_passthrough_if)::set(null, "*.env", "spi_passthrough_vif",
                                                 spi_passthrough_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent*", "vif", tl_if);
    uvm_config_db#(virtual spi_if)::set(null, "*.env.m_spi_agent*", "vif", spi_if);
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

  `ASSERT(Sck_A,   passthrough_i.passthrough_en -> passthrough_i.sck == cio_sck_o, clk, !rst_n)
  `ASSERT(Sck_En_A,passthrough_i.passthrough_en -> passthrough_i.sck_en == cio_sck_en_o,
          clk, !rst_n)
  `ASSERT(Csb_A,   passthrough_i.passthrough_en -> passthrough_i.csb == cio_csb_o, clk, !rst_n)
  `ASSERT(Csb_En_A,passthrough_i.passthrough_en -> passthrough_i.csb_en == cio_csb_en_o,
          clk, !rst_n)
  `ASSERT(S_En_A,  passthrough_i.passthrough_en -> passthrough_i.s_en == cio_sd_en_o, clk, !rst_n)
  `ASSERT(Sd_O_A,  passthrough_i.passthrough_en -> passthrough_i.s == cio_sd_o, clk, !rst_n)
  `ASSERT(Sd_I_A,  passthrough_i.passthrough_en -> passthrough_o.s == cio_sd_i, clk, !rst_n)

endmodule
