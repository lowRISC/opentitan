############
# Boot ROM #
############
# We need to enforce a defined placement of the Boot ROM to enable the Boot ROM splicing script.
# Any change in ROM instances path should be updated in following two files
# 1. hw/top_earlgrey/data/placement.xdc and
# 2. hw/top_earlgrey/util/vivado_hook_opt_design_post.tcl
set_property LOC RAMB36_X0Y10 [get_cells -hierarchical -filter { NAME =~ "*u_rom_ctrl*u_rom*rdata_o_reg_0" && PRIMITIVE_TYPE =~ BMEM.*.* }]
set_property LOC RAMB36_X0Y11 [get_cells -hierarchical -filter { NAME =~ "*u_rom_ctrl*u_rom*rdata_o_reg_1" && PRIMITIVE_TYPE =~ BMEM.*.* }]
set_property LOC RAMB36_X0Y12 [get_cells -hierarchical -filter { NAME =~ "*u_rom_ctrl*u_rom*rdata_o_reg_2" && PRIMITIVE_TYPE =~ BMEM.*.* }]
set_property LOC RAMB36_X0Y13 [get_cells -hierarchical -filter { NAME =~ "*u_rom_ctrl*u_rom*rdata_o_reg_3" && PRIMITIVE_TYPE =~ BMEM.*.* }]
set_property LOC RAMB36_X0Y14 [get_cells -hierarchical -filter { NAME =~ "*u_rom_ctrl*u_rom*rdata_o_reg_4" && PRIMITIVE_TYPE =~ BMEM.*.* }]

###############
# Guiding P&R #
###############
# Additional placement rules are for guiding P&R to:
# - speed up implementation time, and
# - improve reproducibility of SCA measurements.
#
# These rules might need to be adjusted from time to time as the design changes. They can be
# extracted from an implemented design using the following commands:
#
#   set BRAMS [get_cells -hierarchical -filter { PRIMITIVE_TYPE =~ BMEM.* }]
#
#   foreach i $BRAMS {puts "set_property LOC [get_property LOC [get_cells $i]] \[get_cells $i\]" }
#
# OTP
set_property LOC RAMB18_X1Y71 [get_cells top_earlgrey/u_otp_ctrl/u_otp/gen_generic.u_impl_generic/u_prim_ram_1p_adv/u_mem/gen_generic.u_impl_generic/mem_reg_0]

# Flash
set_property LOC RAMB36_X8Y36  [get_cells top_earlgrey/u_flash_ctrl/u_eflash/u_flash/gen_generic.u_impl_generic/gen_prim_flash_banks[0].u_prim_flash_bank/gen_info_types[0].u_info_mem/gen_generic.u_impl_generic/mem_reg_0]
set_property LOC RAMB36_X7Y55  [get_cells top_earlgrey/u_flash_ctrl/u_eflash/u_flash/gen_generic.u_impl_generic/gen_prim_flash_banks[0].u_prim_flash_bank/gen_info_types[0].u_info_mem_meta/gen_generic.u_impl_generic/mem_reg_0]
set_property LOC RAMB36_X7Y32  [get_cells top_earlgrey/u_flash_ctrl/u_eflash/u_flash/gen_generic.u_impl_generic/gen_prim_flash_banks[0].u_prim_flash_bank/u_mem/gen_generic.u_impl_generic/mem_reg_0_0]
set_property LOC RAMB36_X10Y55 [get_cells top_earlgrey/u_flash_ctrl/u_eflash/u_flash/gen_generic.u_impl_generic/gen_prim_flash_banks[0].u_prim_flash_bank/u_mem_meta/gen_generic.u_impl_generic/mem_reg_0_0]
set_property LOC RAMB36_X3Y55  [get_cells top_earlgrey/u_flash_ctrl/u_eflash/u_flash/gen_generic.u_impl_generic/gen_prim_flash_banks[1].u_prim_flash_bank/gen_info_types[0].u_info_mem/gen_generic.u_impl_generic/mem_reg_0]
set_property LOC RAMB36_X5Y55  [get_cells top_earlgrey/u_flash_ctrl/u_eflash/u_flash/gen_generic.u_impl_generic/gen_prim_flash_banks[1].u_prim_flash_bank/gen_info_types[0].u_info_mem_meta/gen_generic.u_impl_generic/mem_reg_0]
set_property LOC RAMB36_X0Y58  [get_cells top_earlgrey/u_flash_ctrl/u_eflash/u_flash/gen_generic.u_impl_generic/gen_prim_flash_banks[1].u_prim_flash_bank/u_mem/gen_generic.u_impl_generic/mem_reg_0_0]
set_property LOC RAMB36_X5Y59  [get_cells top_earlgrey/u_flash_ctrl/u_eflash/u_flash/gen_generic.u_impl_generic/gen_prim_flash_banks[1].u_prim_flash_bank/u_mem_meta/gen_generic.u_impl_generic/mem_reg_0_0]
set_property LOC RAMB18_X2Y82  [get_cells top_earlgrey/u_flash_ctrl/u_eflash/u_flash/gen_generic.u_impl_generic/u_cfg_ram/gen_generic.u_impl_generic/mem_reg_0]

# Main SRAM
set_property LOC RAMB36_X3Y43 [get_cells top_earlgrey/u_sram_ctrl_main/u_prim_ram_1p_scr/u_prim_ram_1p_adv/u_mem/gen_generic.u_impl_generic/mem_reg_0_0]

# Retention RAM
set_property LOC RAMB36_X3Y46 [get_cells top_earlgrey/u_sram_ctrl_ret_aon/u_prim_ram_1p_scr/u_prim_ram_1p_adv/u_mem/gen_generic.u_impl_generic/mem_reg_0]
set_property LOC RAMB18_X4Y90 [get_cells top_earlgrey/u_sram_ctrl_ret_aon/u_prim_ram_1p_scr/u_prim_ram_1p_adv/u_mem/gen_generic.u_impl_generic/mem_reg_1]

# OTBN
set_property LOC RAMB36_X2Y8 [get_cells top_earlgrey/u_otbn/u_dmem/u_prim_ram_1p_adv/u_mem/gen_generic.u_impl_generic/mem_reg_0]
set_property LOC RAMB36_X2Y5 [get_cells top_earlgrey/u_otbn/u_imem/u_prim_ram_1p_adv/u_mem/gen_generic.u_impl_generic/mem_reg_0]
set_property LOC RAMB18_X2Y8 [get_cells top_earlgrey/u_otbn/u_imem/u_prim_ram_1p_adv/u_mem/gen_generic.u_impl_generic/mem_reg_1]

# Ibex
set_property LOC RAMB36_X8Y21 [get_cells top_earlgrey/u_rv_core_ibex/u_core/gen_rams.gen_rams_inner[0].data_bank/gen_generic.u_impl_generic/mem_reg_0]
set_property LOC RAMB18_X8Y40 [get_cells top_earlgrey/u_rv_core_ibex/u_core/gen_rams.gen_rams_inner[0].data_bank/gen_generic.u_impl_generic/mem_reg_1]
set_property LOC RAMB18_X6Y40 [get_cells top_earlgrey/u_rv_core_ibex/u_core/gen_rams.gen_rams_inner[0].tag_bank/gen_generic.u_impl_generic/mem_reg]
set_property LOC RAMB36_X8Y22 [get_cells top_earlgrey/u_rv_core_ibex/u_core/gen_rams.gen_rams_inner[1].data_bank/gen_generic.u_impl_generic/mem_reg_0]
set_property LOC RAMB18_X8Y41 [get_cells top_earlgrey/u_rv_core_ibex/u_core/gen_rams.gen_rams_inner[1].data_bank/gen_generic.u_impl_generic/mem_reg_1]
set_property LOC RAMB18_X6Y41 [get_cells top_earlgrey/u_rv_core_ibex/u_core/gen_rams.gen_rams_inner[1].tag_bank/gen_generic.u_impl_generic/mem_reg]
