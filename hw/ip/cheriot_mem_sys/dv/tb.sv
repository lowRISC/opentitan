// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
module tb;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import cheriot_mem_sys_env_pkg::*;
  import cheriot_mem_sys_test_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  wire clk, rst_n, rst_shadowed_n;
  wire [NUM_MAX_INTERRUPTS-1:0] interrupts;

  // interfaces
  clk_rst_if clk_rst_if(.clk(clk), .rst_n(rst_n));
  rst_shadowed_if rst_shad_if(.rst_n(rst_n), .rst_shadowed_n(rst_shadowed_n));
  tl_if tl_if(.clk(clk), .rst_n(rst_n));
  pins_if #(NUM_MAX_INTERRUPTS) intr_if(.pins(interrupts));

  // Requests of the host ports, which this testbench only observes
  tlul_pkg::tl_h2d_t cored_tl_h, tbre_tl_h, meta_sram_tl;

  `DV_ALERT_IF_CONNECT()

  // The memory map this testbench builds the DUT with; the sequences use the same values
  localparam tagged_regions_t TaggedRegions = '{
      main_sram_base: 32'h1000_0000, main_sram_top: 32'h1003_0000,
      nvm_base:       32'h3000_0000, nvm_top:       32'h3020_0000};
  localparam logic [31:0] MetaSramBaseAddr = 32'h1100_0000;
  localparam int unsigned MemSizeRevbm     = 3072;  // the revocation bitmap of the main SRAM

  // dut
  cheriot_mem_sys #(
    .MainSramBaseAddr     (TaggedRegions.main_sram_base),
    .MainSramTopAddr      (TaggedRegions.main_sram_top ),
    .NvmBaseAddr          (TaggedRegions.nvm_base      ),
    .NvmTopAddr           (TaggedRegions.nvm_top       ),
    .MetaSramBaseAddr     (MetaSramBaseAddr            ),
    .MemSizeRevbm         (MemSizeRevbm                )
  ) dut (
    .clk_i                (clk      ),
    .rst_ni               (rst_n    ),
    .rst_shadowed_ni      (rst_shadowed_n),

    // Scan mode off
    .scanmode_i           (prim_mubi_pkg::MuBi4False),
    .scan_rst_ni          (1'b1),

    // Bus interface (device) for CSRs
    .regs_tl_d_i          (tl_if.h2d),
    .regs_tl_d_o          (tl_if.d2h),

    // Interrupts
    .intr_tbre_done_o     (interrupts[0]),

    // Alerts
    .alert_rx_i           (alert_rx ),
    .alert_tx_o           (alert_tx ),

    // Execution mode
    .cheriot_ena_i        (prim_mubi_pkg::MuBi4False),
    .cheriot_ena_shadow_i (prim_mubi_pkg::MuBi4False),
    .cheriot_ena_cmp_i    (prim_mubi_pkg::MuBi4False),

    // Core data port with its capability tag sideband
    .cored_tl_d_i         (tlul_pkg::TL_H2D_DEFAULT),
    .cored_tag_h2d_i      (prim_mubi_pkg::MuBi4False),
    .cored_tl_d_o         (),
    .cored_tag_d2h_o      (),

    // Core revocation bitmap port
    .corerevbm_tl_i       (tlul_pkg::TL_H2D_DEFAULT),
    .corerevbm_tl_o       (),

    // System revocation bitmap window
    .revbm_tl_d_i         (tlul_pkg::TL_H2D_DEFAULT),
    .revbm_tl_d_o         (),

    // Host port towards the interconnect
    .cored_tl_h_o         (cored_tl_h),
    .cored_tl_h_i         (tlul_pkg::TL_D2H_DEFAULT),
    // The revocation engine is not exercised in this environment yet
    .tbre_tl_h_o          (tbre_tl_h),
    .tbre_tl_h_i          (tlul_pkg::TL_D2H_DEFAULT),

    // Host port towards the meta SRAM
    .meta_sram_tl_o       (meta_sram_tl),
    .meta_sram_tl_i       (tlul_pkg::TL_D2H_DEFAULT)
  );

  // The testbench runs in ePMP mode and never drives the core ports, and a sweep cannot start
  // outside CHERIoT mode (see TBRE_START), so no host port may ever request anything.
  `ASSERT(CoredHostIdle_A, !cored_tl_h.a_valid, clk, !rst_n)
  `ASSERT(TbreHostIdle_A, !tbre_tl_h.a_valid, clk, !rst_n)
  `ASSERT(MetaSramHostIdle_A, !meta_sram_tl.a_valid, clk, !rst_n)

  initial begin
    // drive clk and rst_n from clk_if
    clk_rst_if.set_active();
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(virtual rst_shadowed_if)::set(null, "*.env", "rst_shadowed_vif", rst_shad_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent*", "vif", tl_if);
    uvm_config_db#(intr_vif)::set(null, "*.env", "intr_vif", intr_if);
    uvm_config_db#(tagged_regions_t)::set(null, "*.env", "tagged_regions", TaggedRegions);
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

endmodule
