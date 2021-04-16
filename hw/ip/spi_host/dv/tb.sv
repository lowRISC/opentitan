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

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  wire clk, rst_n;
  wire clk_core, rst_core_n;
  wire devmode;
  wire [NUM_MAX_INTERRUPTS-1:0] interrupts;

  lc_tx_t           scanmode_i;
  wire              cio_sck_o;
  wire              cio_sck_en_o;
  wire  [NumCS-1:0] cio_csb_o;
  wire  [NumCS-1:0] cio_csb_en_o;
  logic [3:0]       cio_sd_o;
  logic [3:0]       cio_sd_en_o;
  logic [3:0]       cio_sd_i;
  logic             intr_error;
  logic             intr_event;

  // interfaces
  clk_rst_if   clk_rst_if(.clk(clk), .rst_n(rst_n));
  clk_rst_if   clk_rst_core_if(.clk(clk_core), .rst_n(rst_core_n));
  pins_if #(1) devmode_if(devmode);
  pins_if #(NUM_MAX_INTERRUPTS) intr_if(.pins(interrupts));
  tl_if        tl_if(.clk(clk), .rst_n(rst_n));
  spi_if       spi_if(.rst_n(rst_core_n));

  // dut
  spi_host dut (
    .clk_i                (clk),
    .rst_ni               (rst_n),

    // tl i/f
    .tl_i                 (tl_if.h2d),
    .tl_o                 (tl_if.d2h),
    // scan mode
    .clk_core_i           (clk_core),
    .rst_core_ni          (rst_core_n),
    .scanmode_i           (scanmode_i),
    // spi i/o
    .cio_sck_o            (cio_sck_o),
    .cio_sck_en_o         (cio_sck_en_o),
    .cio_csb_o            (cio_csb_o),
    .cio_csb_en_o         (cio_csb_en_o),
    .cio_sd_o             (cio_sd_o),
    .cio_sd_en_o          (cio_sd_en_o),
    .cio_sd_i             (cio_sd_i),
    // intr i/f
    .intr_error_o         (intr_error),
    .intr_spi_event_o     (intr_event)
  );

  assign spi_if.sck = (cio_sck_en_o) ? cio_sck_o : 1'bz;
  assign cio_sd_i   = spi_if.sio;
  always_comb begin
    for (int i = 0; i < 4; i++) begin
      if (cio_sd_en_o[i]) begin
        spi_if.sio[i] = cio_sd_o[i];
      end
      if (i < NumCS) begin
        spi_if.csb[i] = (cio_csb_en_o[i]) ? cio_csb_o[i] : 1'b1;
      end else begin
        spi_if.csb[i] = 1'b1;
      end
    end
  end

  assign interrupts[SpiHostError] = intr_error;
  assign interrupts[SpiHostEvent] = intr_event;
  
  initial begin
    // drive clk and rst_n from clk_if
    clk_rst_if.set_active();
    clk_rst_core_if.set_active();
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_core_vif", clk_rst_core_if);
    uvm_config_db#(intr_vif)::set(null, "*.env", "intr_vif", intr_if);
    uvm_config_db#(devmode_vif)::set(null, "*.env", "devmode_vif", devmode_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent*", "vif", tl_if);
    uvm_config_db#(virtual spi_if)::set(null, "*.env.m_spi_agent*", "vif", spi_if);
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

endmodule
