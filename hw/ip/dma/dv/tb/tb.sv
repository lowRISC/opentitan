// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module tb;
  // Dependencies - Packages and Macros
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import tlul_pkg::*;
  import dma_pkg::*;
  import dma_env_pkg::*;
  import dma_test_pkg::*;

  `include "uvm_macros.svh"
  `include "dv_macros.svh"
  `include "cip_macros.svh"

  // Common Interface - Clock and Reset
  wire        clk;
  wire        rst_n;
  clk_rst_if  clk_rst_if(.clk(clk), .rst_n(rst_n));

  // Common wire - Handshake/Interrupt Inputs
  wire                     handshake_i;
  dma_if #(.WIDTH_IN(1))   dma_intf(.clk_i(clk), .rst_ni(rst_n));
  assign handshake_i = dma_intf.handshake_i;

  // Common Interface - Interrupt Outputs
  wire [NUM_MAX_INTERRUPTS-1:0] interrupts;
  pins_if #(NUM_MAX_INTERRUPTS) intr_if(interrupts);

  // CIP Interface
  wire         devmode;
  pins_if #(1) devmode_if (devmode);

  // TL Interface
  tl_if tl_if            (.clk(clk), .rst_n(rst_n)); // Ingress Port from System Fabric *Primary*
  tl_if tl_host_device_if(.clk(clk), .rst_n(rst_n)); // Egress Port to System Fabric (DMA Registers)
  tl_if tl_xbar_device_if(.clk(clk), .rst_n(rst_n)); // to CTN XBar

  `DV_ALERT_IF_CONNECT()

  // Instantiate DUT
  dma #(
    .EnableDataIntgGen (1)
  ) dut (
    .clk_i           (clk),
    .rst_ni          (rst_n),
    .test_en_i       (1'b0), // TODO (DV) update

    .lsio_trigger_i  (handshake_i),
    .intr_dma_o      (interrupts[0]),

    .alert_rx_i      (alert_rx),
    .alert_tx_o      (alert_tx),

    // TL Interface
    .tl_host_o       (tl_host_device_if.h2d),
    .tl_host_i       (tl_host_device_if.d2h),

    // TL Interface for CSR
    .tl_dev_o        (tl_if.h2d),
    .tl_dev_i        (tl_if.d2h),

    .tl_xbar_o       (tl_xbar_device_if.h2d),
    .tl_xbar_i       (tl_xbar_device_if.d2h),

    .sys_o           (),
    .sys_i           ('0)
  );

  // assign dma_intf.remaining     = dut.remaining_bytes; // Add after implementation is done
  assign dma_intf.read_cmpl_host = dut.tl_host_i.d_valid;
  assign dma_intf.read_cmpl_xbar = dut.tl_xbar_i.d_valid;

  assign dma_intf.read_opc_host = dut.tl_host_i.d_opcode;
  assign dma_intf.read_opc_xbar = dut.tl_xbar_i.d_opcode;


  // Clocking related
  bit clk_100mhz;
  initial begin
    forever #5ns clk_100mhz <= ~clk_100mhz;
  end

  // Main Block for Initialization
  initial begin
    clk_rst_if.set_active();
    dma_intf.init();

    // Registeration
    uvm_config_db #(virtual tl_if)::set(null, "*.env.m_tl_agent_dma_reg_block*", "vif", tl_if);
    uvm_config_db #(virtual tl_if)::set(null, "*.env.m_tl_agent_dma_host*", "vif",
                                        tl_host_device_if);
    uvm_config_db #(virtual tl_if)::set(null, "*.env.m_tl_agent_dma_xbar*", "vif",
                                        tl_xbar_device_if);
    uvm_config_db #(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db #(virtual dma_if)::set(null, "*.env", "dma_vif", dma_intf);
    uvm_config_db #(devmode_vif)::set(null, "*.env", "devmode_vif", devmode_if);
    uvm_config_db #(intr_vif)::set(null, "*.env", "intr_vif", intr_if);

    $timeformat(-12, 0, "ps", 12);
    run_test();
  end

endmodule
