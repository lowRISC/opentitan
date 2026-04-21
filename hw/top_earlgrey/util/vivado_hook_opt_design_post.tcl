# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Hook to check BRAM implementation for Boot ROM. This is required for Boot ROM splicing.
send_msg "Designcheck 2-1" INFO "Checking if Boot ROM is mapped to BRAM."

set fpga_family [get_property FAMILY [get_parts [get_property PART [current_design]]]]

switch ${fpga_family} {
  kintex7 {
    set bram_regex "BMEM.*.*"
  }
  kintexu {
    set bram_regex "BLOCKRAM.*.*"
  }
  default {
    set bram_regex "BMEM.*.*"
  }
}

if {[catch [get_cells -hierarchical -filter " NAME =~  *u_rom_ctrl*rdata_o_reg_0_0 && PRIMITIVE_TYPE =~ ${bram_regex} "]]\
 && [catch [get_cells -hierarchical -filter " NAME =~  *u_rom_ctrl*rdata_o_reg_0_1 && PRIMITIVE_TYPE =~ ${bram_regex} "]]\
 && [catch [get_cells -hierarchical -filter " NAME =~  *u_rom_ctrl*rdata_o_reg_0_10 && PRIMITIVE_TYPE =~ ${bram_regex} "]]\
 && [catch [get_cells -hierarchical -filter " NAME =~  *u_rom_ctrl*rdata_o_reg_0_11 && PRIMITIVE_TYPE =~ ${bram_regex} "]]\
 && [catch [get_cells -hierarchical -filter " NAME =~  *u_rom_ctrl*rdata_o_reg_0_12 && PRIMITIVE_TYPE =~ ${bram_regex} "]]\
 && [catch [get_cells -hierarchical -filter " NAME =~  *u_rom_ctrl*rdata_o_reg_0_13 && PRIMITIVE_TYPE =~ ${bram_regex} "]]\
 && [catch [get_cells -hierarchical -filter " NAME =~  *u_rom_ctrl*rdata_o_reg_0_14 && PRIMITIVE_TYPE =~ ${bram_regex} "]]\
 && [catch [get_cells -hierarchical -filter " NAME =~  *u_rom_ctrl*rdata_o_reg_0_15 && PRIMITIVE_TYPE =~ ${bram_regex} "]]\
 && [catch [get_cells -hierarchical -filter " NAME =~  *u_rom_ctrl*rdata_o_reg_0_16 && PRIMITIVE_TYPE =~ ${bram_regex} "]]\
 && [catch [get_cells -hierarchical -filter " NAME =~  *u_rom_ctrl*rdata_o_reg_0_17 && PRIMITIVE_TYPE =~ ${bram_regex} "]]\
 && [catch [get_cells -hierarchical -filter " NAME =~  *u_rom_ctrl*rdata_o_reg_0_18 && PRIMITIVE_TYPE =~ ${bram_regex} "]]\
 && [catch [get_cells -hierarchical -filter " NAME =~  *u_rom_ctrl*rdata_o_reg_0_19 && PRIMITIVE_TYPE =~ ${bram_regex} "]]\
 && [catch [get_cells -hierarchical -filter " NAME =~  *u_rom_ctrl*rdata_o_reg_0_2 && PRIMITIVE_TYPE =~ ${bram_regex} "]]\
 && [catch [get_cells -hierarchical -filter " NAME =~  *u_rom_ctrl*rdata_o_reg_0_20 && PRIMITIVE_TYPE =~ ${bram_regex} "]]\
 && [catch [get_cells -hierarchical -filter " NAME =~  *u_rom_ctrl*rdata_o_reg_0_21 && PRIMITIVE_TYPE =~ ${bram_regex} "]]\
 && [catch [get_cells -hierarchical -filter " NAME =~  *u_rom_ctrl*rdata_o_reg_0_22 && PRIMITIVE_TYPE =~ ${bram_regex} "]]\
 && [catch [get_cells -hierarchical -filter " NAME =~  *u_rom_ctrl*rdata_o_reg_0_23 && PRIMITIVE_TYPE =~ ${bram_regex} "]]\
 && [catch [get_cells -hierarchical -filter " NAME =~  *u_rom_ctrl*rdata_o_reg_0_24 && PRIMITIVE_TYPE =~ ${bram_regex} "]]\
 && [catch [get_cells -hierarchical -filter " NAME =~  *u_rom_ctrl*rdata_o_reg_0_25 && PRIMITIVE_TYPE =~ ${bram_regex} "]]\
 && [catch [get_cells -hierarchical -filter " NAME =~  *u_rom_ctrl*rdata_o_reg_0_26 && PRIMITIVE_TYPE =~ ${bram_regex} "]]\
 && [catch [get_cells -hierarchical -filter " NAME =~  *u_rom_ctrl*rdata_o_reg_0_27 && PRIMITIVE_TYPE =~ ${bram_regex} "]]\
 && [catch [get_cells -hierarchical -filter " NAME =~  *u_rom_ctrl*rdata_o_reg_0_28 && PRIMITIVE_TYPE =~ ${bram_regex} "]]\
 && [catch [get_cells -hierarchical -filter " NAME =~  *u_rom_ctrl*rdata_o_reg_0_29 && PRIMITIVE_TYPE =~ ${bram_regex} "]]\
 && [catch [get_cells -hierarchical -filter " NAME =~  *u_rom_ctrl*rdata_o_reg_0_3 && PRIMITIVE_TYPE =~ ${bram_regex} "]]\
 && [catch [get_cells -hierarchical -filter " NAME =~  *u_rom_ctrl*rdata_o_reg_0_30 && PRIMITIVE_TYPE =~ ${bram_regex} "]]\
 && [catch [get_cells -hierarchical -filter " NAME =~  *u_rom_ctrl*rdata_o_reg_0_31 && PRIMITIVE_TYPE =~ ${bram_regex} "]]\
 && [catch [get_cells -hierarchical -filter " NAME =~  *u_rom_ctrl*rdata_o_reg_0_32 && PRIMITIVE_TYPE =~ ${bram_regex} "]]\
 && [catch [get_cells -hierarchical -filter " NAME =~  *u_rom_ctrl*rdata_o_reg_0_33 && PRIMITIVE_TYPE =~ ${bram_regex} "]]\
 && [catch [get_cells -hierarchical -filter " NAME =~  *u_rom_ctrl*rdata_o_reg_0_34 && PRIMITIVE_TYPE =~ ${bram_regex} "]]\
 && [catch [get_cells -hierarchical -filter " NAME =~  *u_rom_ctrl*rdata_o_reg_0_35 && PRIMITIVE_TYPE =~ ${bram_regex} "]]\
 && [catch [get_cells -hierarchical -filter " NAME =~  *u_rom_ctrl*rdata_o_reg_0_36 && PRIMITIVE_TYPE =~ ${bram_regex} "]]\
 && [catch [get_cells -hierarchical -filter " NAME =~  *u_rom_ctrl*rdata_o_reg_0_37 && PRIMITIVE_TYPE =~ ${bram_regex} "]]\
 && [catch [get_cells -hierarchical -filter " NAME =~  *u_rom_ctrl*rdata_o_reg_0_38 && PRIMITIVE_TYPE =~ ${bram_regex} "]]\
 && [catch [get_cells -hierarchical -filter " NAME =~  *u_rom_ctrl*rdata_o_reg_0_4 && PRIMITIVE_TYPE =~ ${bram_regex} "]]\
 && [catch [get_cells -hierarchical -filter " NAME =~  *u_rom_ctrl*rdata_o_reg_0_5 && PRIMITIVE_TYPE =~ ${bram_regex} "]]\
 && [catch [get_cells -hierarchical -filter " NAME =~  *u_rom_ctrl*rdata_o_reg_0_6 && PRIMITIVE_TYPE =~ ${bram_regex} "]]\
 && [catch [get_cells -hierarchical -filter " NAME =~  *u_rom_ctrl*rdata_o_reg_0_7 && PRIMITIVE_TYPE =~ ${bram_regex} "]]\
 && [catch [get_cells -hierarchical -filter " NAME =~  *u_rom_ctrl*rdata_o_reg_0_8 && PRIMITIVE_TYPE =~ ${bram_regex} "]]\
 && [catch [get_cells -hierarchical -filter " NAME =~  *u_rom_ctrl*rdata_o_reg_0_9 && PRIMITIVE_TYPE =~ ${bram_regex} "]] } {
  send_msg "Designcheck 2-2" INFO "BRAM implementation found for Boot ROM."
} else {
  send_msg "Designcheck 2-3" ERROR "BRAM implementation not found for Boot ROM."
}
