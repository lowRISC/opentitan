# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Hook to check BRAM implementation for Boot ROM. This is required for Boot ROM splicing.
send_msg "Designcheck 2-1" INFO "Checking if Boot ROM is mapped to BRAM."

if {[catch [get_cells -hierarchical -filter { NAME =~  "*u_rom_ctrl*u_rom*rdata_o_reg_0" && PRIMITIVE_TYPE =~ BMEM.*.* }]]\
 && [catch [get_cells -hierarchical -filter { NAME =~  "*u_rom_ctrl*u_rom*rdata_o_reg_1" && PRIMITIVE_TYPE =~ BMEM.*.* }]]\
 && [catch [get_cells -hierarchical -filter { NAME =~  "*u_rom_ctrl*u_rom*rdata_o_reg_2" && PRIMITIVE_TYPE =~ BMEM.*.* }]]\
 && [catch [get_cells -hierarchical -filter { NAME =~  "*u_rom_ctrl*u_rom*rdata_o_reg_3" && PRIMITIVE_TYPE =~ BMEM.*.* }]] } {
  send_msg "Designcheck 2-2" INFO "BRAM implementation found for Boot ROM."
} else {
  send_msg "Designcheck 2-3" ERROR "BRAM implementation not found for Boot ROM."
}
