// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
module tb;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import kmac_env_pkg::*;
  import kmac_test_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  wire clk, rst_n;
  wire devmode;
  wire [NUM_MAX_INTERRUPTS-1:0] interrupts;
  // Interrupt wires
  wire intr_kmac_done, intr_kmac_fifo_empty, intr_kmac_err;

  // interfaces
  clk_rst_if clk_rst_if(.clk(clk), .rst_n(rst_n));
  pins_if #(NUM_MAX_INTERRUPTS) intr_if(interrupts);
  pins_if #(1) devmode_if(devmode);
  tl_if tl_if(.clk(clk), .rst_n(rst_n));

  // dut
  kmac dut (
    .clk_i                (clk                  ),
    .rst_ni               (rst_n                ),

    // TLUL interface
    .tl_i                 (tl_if.h2d            ),
    .tl_o                 (tl_if.d2h            ),

    // Interrupts
    .intr_kmac_done_o     (intr_kmac_done       ),
    .intr_fifo_empty_o    (intr_kmac_fifo_empty ),
    .intr_kmac_err_o      (intr_kmac_err        )

    // TODO: hook up interfaces for:
    //
    // 1) keymgr sideload
    // 2) keymgr KDF
    // 3) csrng/edn
  );

  // Bind interrupt wires to interrupt interface
  assign interrupts[KmacDone]       = intr_kmac_done;
  assign interrupts[KmacFifoEmpty]  = intr_kmac_fifo_empty;
  assign interrupts[KmacErr]        = intr_kmac_done;

  initial begin
    // drive clk and rst_n from clk_if
    clk_rst_if.set_active();
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(intr_vif)::set(null, "*.env", "intr_vif", intr_if);
    uvm_config_db#(devmode_vif)::set(null, "*.env", "devmode_vif", devmode_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent*", "vif", tl_if);
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

endmodule
