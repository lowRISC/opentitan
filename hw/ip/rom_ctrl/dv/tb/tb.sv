// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
module tb;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import rom_ctrl_env_pkg::*;
  import rom_ctrl_test_pkg::*;
  import rom_ctrl_bkdr_util_pkg::rom_ctrl_bkdr_util;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"
  // Describes the layout of the ROM memory array of whichever prim_rom implementation is mapped in
  // for this build.
  `include "rom_ctrl_bkdr_util_hier.svh"

  // dut
  rom_ctrl #(
    .RndCnstScrNonce      (RND_CNST_SCR_NONCE),
    .RndCnstScrKey        (RND_CNST_SCR_KEY),
    // ROM size in bytes
    .MemSizeRom           (ROM_SIZE_BYTES)
   ) dut (
    // Interaction with these ports is through u_bound_if
    .clk_i                (),
    .rst_ni               (),

    .rom_cfg_i            (prim_rom_pkg::ROM_CFG_REQ_DEFAULT),
    .rom_cfg_o            (),

    // Interaction with these ports is through u_bound_if
    .rom_tl_i             (),
    .rom_tl_o             (),
    .regs_tl_i            (),
    .regs_tl_o            (),
    .alert_rx_i           (),
    .alert_tx_o           (),
    .pwrmgr_data_o        (),
    .keymgr_data_o        (),
    .kmac_data_i          (),
    .kmac_data_o          ()
  );

  // Bind rom_ctrl_bound_if into the instance of rom_ctrl.
  //
  // It is active in this tb, which means that the rom_ctrl_if inside is also active and drives the
  // rom_ctrl input ports (which are not explicitly connected above).
  //
  // The two-layer design allows the bound interface depend on parameters and be able to access more
  // of the internals of the design (without needing to parameterise the environment).
  bind dut
    rom_ctrl_bound_if #(.Bound(1), .SecDisableScrambling(SecDisableScrambling))
    u_bound_if (
      .clk           (clk_i),
      .rst_n         (rst_ni),
      .rom_h2d       (rom_tl_i),
      .rom_d2h       (rom_tl_o),
      .regs_h2d      (regs_tl_i),
      .regs_d2h      (regs_tl_o),
      .alert_rx      (alert_rx_i),
      .alert_tx      (alert_tx_o),
      .pwrmgr_data   (pwrmgr_data_o),
      .keymgr_data   (keymgr_data_o),
      .kmac_req_data (kmac_data_o),
      .kmac_rsp_data (kmac_data_i)
    );

  // Bind a rom_ctrl_fsm_if into the fsm module (allowing DV to get its internal values and
  // parameters)
  bind dut.gen_fsm_scramble_enabled.u_checker_fsm
     rom_ctrl_fsm_bound_if #(.Bound(1), .TopCount(TopCount))
     u_bound_if (.clk_i, .rst_ni);

  // Bind a rom_ctrl_compare_bound_if into the compare module, which will be able to access
  // internal design signals and parameters. It will instantiate a (non-parameterised)
  // rom_ctrl_compare_if inside it, which can be passed to the environment.
  bind dut.gen_fsm_scramble_enabled.u_checker_fsm.u_compare
    rom_ctrl_compare_bound_if #(.Bound(1),
                                .StateWidth($bits(Waiting)), .Waiting (Waiting), .Done (Done),
                                .AW (AW), .LastAddr (LastAddr))
       u_bound_if (
         .clk_i     (clk_i),
         .rst_ni    (rst_ni),
         .addr_q_i  (addr_q),
         .state_q_i (state_q),
         .state_d_i (state_d)
       );

  // Instantiate the memory backdoor util instance.
  //
  // `ROM_CTRL_MEM_HIER` is the `prim_rom` instance, not the memory array: the ROM may be composed
  // of several arrays (one per tile), so depth and width are derived from one tile and scaled by
  // the number of tiles.
  `define ROM_CTRL_MEM_HIER \
    tb.dut.gen_rom_scramble_enabled.u_rom.u_rom.u_prim_rom
  `define ROM_CTRL_MEM_TILE_HIER `ROM_CTRL_MEM_HIER.`ROM_MEM_TILE_PATH

  initial begin
    rom_ctrl_bkdr_util m_rom_ctrl_bkdr_util;
    m_rom_ctrl_bkdr_util = new(.name  ("rom_ctrl_bkdr_util"),
                               .path  (`ROM_MEM_BKDR_PATH(`ROM_CTRL_MEM_HIER)),
                               .depth (`ROM_MEM_NUM_TILES *
                                       $size(`ROM_CTRL_MEM_TILE_HIER)),
                               .n_bits(`ROM_MEM_NUM_TILES *
                                       $bits(`ROM_CTRL_MEM_TILE_HIER)),
                               .err_detection_scheme(mem_bkdr_util_pkg::EccInv_39_32),
                               .key(dut.RndCnstScrKey), .nonce(dut.RndCnstScrNonce),
                               .tiling_path(`ROM_MEM_TILING_PATH),
                               .tiling_suffix_fmt_str(`ROM_MEM_TILING_FMT),
                               .tile_depth($size(`ROM_CTRL_MEM_TILE_HIER)));

    // Pass interfaces to the environment
    uvm_config_db#(rom_ctrl_vif)::set(null, "*.env", "rom_ctrl_vif",
                                      dut.u_bound_if.gen_bound.u_rom_ctrl_if);
    uvm_config_db#(rom_ctrl_bkdr_util)::set(null, "*.env", "rom_ctrl_bkdr_util",
                                            m_rom_ctrl_bkdr_util);
    uvm_config_db#(virtual rom_ctrl_fsm_if)::set(
        null, "*.env", "rom_ctrl_fsm_vif",
        dut.gen_fsm_scramble_enabled.u_checker_fsm.u_bound_if.gen_bound.u_fsm_if);
    uvm_config_db#(virtual rom_ctrl_compare_if)::set(
        null, "*.env", "rom_ctrl_compare_vif",
        dut.gen_fsm_scramble_enabled.u_checker_fsm.u_compare.u_bound_if.gen_bound.u_compare_if);

    // Pass a flag that tells the environment that we haven't built rom_ctrl without its integrity
    // check FSM.
    uvm_config_db#(bit)::set(null, "*.env", "integrity_check_disabled", 0);

    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

  `undef ROM_CTRL_MEM_TILE_HIER
  `undef ROM_CTRL_MEM_HIER

endmodule
