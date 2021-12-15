// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_rom_ctrl_ast_rom_cfg_vseq extends chip_base_vseq;
  `uvm_object_utils(chip_rom_ctrl_ast_rom_cfg_vseq)

  `uvm_object_new

  localparam string ROM_CFG_SOURCE_PATH = "tb.dut.u_ast.u_ast_dft.sprom_rm_o";
  localparam string ROM_CFG_DEST_PATH = {
    "tb.dut.top_earlgrey.u_rom_ctrl.",
    "gen_rom_scramble_enabled.u_rom.u_rom.u_prim_rom.",
    "gen_generic.u_impl_generic.cfg_i"
  };

  virtual task rom_cfg_conn_check();
    prim_rom_pkg::rom_cfg_t rom_cfg_dest;
    int retval;
    // check hdl paths are valid
    retval = uvm_hdl_check_path(ROM_CFG_SOURCE_PATH);
    `DV_CHECK_EQ_FATAL(retval, 1, $sformatf(
                       "Hierarchical path %0s appears to be invalid.", ROM_CFG_SOURCE_PATH))
    retval = uvm_hdl_check_path(ROM_CFG_DEST_PATH);
    `DV_CHECK_EQ_FATAL(retval, 1, $sformatf(
                       "Hierarchical path %0s appears to be invalid.", ROM_CFG_DEST_PATH))

    // force in turn every possible value onto the source path,
    // read from the destination path then do a check
    // that the forced data has arrived.
    for (int i = 0; i < 2 ** $bits(rom_cfg_dest); i++) begin
      retval = uvm_hdl_force(ROM_CFG_SOURCE_PATH, i);
      `DV_CHECK_EQ(retval, 1, $sformatf("uvm_hdl_force failed for %0s", ROM_CFG_SOURCE_PATH))

      retval = uvm_hdl_read(ROM_CFG_DEST_PATH, rom_cfg_dest);
      `DV_CHECK_EQ(retval, 1, $sformatf("uvm_hdl_read failed for %0s", ROM_CFG_DEST_PATH))

      `DV_CHECK_EQ(
          i, rom_cfg_dest, $sformatf(
          "rom_cfg connectivity check failed, source = 0x%0x, dest = 0x%0x", i, rom_cfg_dest))
    end
  endtask

  virtual task body();
    rom_cfg_conn_check();
  endtask

endclass : chip_rom_ctrl_ast_rom_cfg_vseq
