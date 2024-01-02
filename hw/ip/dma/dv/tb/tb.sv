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
  wire clk;
  wire rst_n;
  clk_rst_if clk_rst_if(.clk(clk), .rst_n(rst_n));

  // Common wire - Handshake/Interrupt Inputs
  wire [dma_reg_pkg::NumIntClearSources - 1 : 0] handshake_i;
  dma_if dma_intf(.clk_i(clk), .rst_ni(rst_n));
  assign handshake_i = dma_intf.handshake_i;

  // Common Interface - Interrupt Outputs
  wire [NUM_MAX_INTERRUPTS - 1 : 0] interrupts;
  pins_if #(NUM_MAX_INTERRUPTS) intr_if(interrupts);

  // CIP Interface
  wire devmode;
  pins_if #(1) devmode_if (devmode);

  // TL Interface
  tl_if tl_if (.clk(clk), .rst_n(rst_n)); // Ingress Port from System Fabric *Primary*
  tl_if tl_host_if(.clk(clk), .rst_n(rst_n)); // Egress Port to System Fabric (DMA Registers)
  tl_if tl_ctn_if(.clk(clk), .rst_n(rst_n)); // to CTN
  tl_if tl_sys_if(.clk(clk), .rst_n(rst_n)); // to SYS

  // Adapter to convert SoC System bus to TL
  dma_sys_tl_if #(.TLAddrWidth(32)) sys_tl_adapter_if(.clk_i(clk), .rst_ni(rst_n));
  assign tl_sys_if.h2d = sys_tl_adapter_if.tl_h2d;
  assign sys_tl_adapter_if.tl_d2h = tl_sys_if.d2h;

  `DV_ALERT_IF_CONNECT()

  // Instantiate DUT
  dma #(
    .EnableDataIntgGen (1)
  ) dut (
    .clk_i (clk),
    .rst_ni (rst_n),
    .scanmode_i (prim_mubi_pkg::MuBi4False),
    .lsio_trigger_i (handshake_i),
    .intr_dma_done_o (interrupts[DMA_DONE]),
    .intr_dma_error_o (interrupts[DMA_ERROR]),
    .intr_dma_memory_buffer_limit_o (interrupts[DMA_MEM_LIMIT]),
    .alert_rx_i (alert_rx),
    .alert_tx_o (alert_tx),
    // TL Interface to OT Internal address space
    .host_tl_h_o (tl_host_if.h2d),
    .host_tl_h_i (tl_host_if.d2h),
    // TL Interface for CSR
    .tl_d_o (tl_if.d2h),
    .tl_d_i (tl_if.h2d),
    // TL Interface to SoC ConTrol Network
    .ctn_tl_h2d_o (tl_ctn_if.h2d),
    .ctn_tl_d2h_i (tl_ctn_if.d2h),
    // SoC System bus
    .sys_o (sys_tl_adapter_if.sys_h2d),
    .sys_i (sys_tl_adapter_if.sys_d2h)
  );

  assign dma_intf.remaining     = dut.remaining_bytes;
  assign dma_intf.read_cmpl_host = tl_host_if.d2h.d_valid;
  assign dma_intf.read_cmpl_ctn = tl_ctn_if.d2h.d_valid;

  assign dma_intf.read_opc_host = tl_host_if.d2h.d_opcode;
  assign dma_intf.read_opc_ctn = tl_ctn_if.d2h.d_opcode;


  // Clocking related
  bit clk_100mhz;
  initial begin
    forever #5ns clk_100mhz <= ~clk_100mhz;
  end

  // Main Block for Initialization
  initial begin
    clk_rst_if.set_active();
    dma_intf.init();

    // Registration
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent_dma_reg_block*", "vif", tl_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.tl_agent_dma_host*", "vif", tl_host_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.tl_agent_dma_ctn*", "vif", tl_ctn_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.tl_agent_dma_sys*", "vif", tl_sys_if);
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(virtual dma_if)::set(null, "*.env", "dma_vif", dma_intf);
    uvm_config_db#(virtual dma_sys_tl_if)::set(null, "*.env", "dma_sys_tl_vif", sys_tl_adapter_if);
    uvm_config_db#(devmode_vif)::set(null, "*.env", "devmode_vif", devmode_if);
    uvm_config_db#(intr_vif)::set(null, "*.env", "intr_vif", intr_if);

    $timeformat(-12, 0, "ps", 12);
    run_test();
  end

endmodule
