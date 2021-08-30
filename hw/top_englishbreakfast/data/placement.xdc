############
# Boot ROM #
############
# We need to enforce a defined placement of the Boot ROM to enable the Boot ROM splicing script.
# Any change in ROM instances path should be updated in following two files
# 1. hw/top_englishbreakfast/data/placement.xdc and
# 2. hw/top_englishbreakfast/util/vivado_hook_opt_design_post.tcl
set_property LOC RAMB36_X0Y10 [get_cells -hierarchical -filter { NAME =~ "*u_rom_ctrl*u_rom*rdata_o_reg_0" && PRIMITIVE_TYPE =~ BMEM.*.* }]
set_property LOC RAMB36_X0Y11 [get_cells -hierarchical -filter { NAME =~ "*u_rom_ctrl*u_rom*rdata_o_reg_1" && PRIMITIVE_TYPE =~ BMEM.*.* }]
set_property LOC RAMB36_X0Y12 [get_cells -hierarchical -filter { NAME =~ "*u_rom_ctrl*u_rom*rdata_o_reg_2" && PRIMITIVE_TYPE =~ BMEM.*.* }]
set_property LOC RAMB36_X0Y13 [get_cells -hierarchical -filter { NAME =~ "*u_rom_ctrl*u_rom*rdata_o_reg_3" && PRIMITIVE_TYPE =~ BMEM.*.* }]
