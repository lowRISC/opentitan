# Any change in ROM instances path should be updated in following two files
# 1. hw/top_earlgrey/data/placement.xdc and
# 2. hw/top_earlgrey/util/vivado_hook_opt_design_post.tcl
set_property LOC RAMB36_X4Y18 [get_cells -hierarchical -filter { NAME =~  "*rom_rom*dout_o_reg_0" && PRIMITIVE_TYPE =~ BMEM.*.* }]
set_property LOC RAMB36_X4Y19 [get_cells -hierarchical -filter { NAME =~  "*rom_rom*dout_o_reg_1" && PRIMITIVE_TYPE =~ BMEM.*.* }]

set_property MARK_DEBUG false [get_nets top_earlgrey/core/u_core/data_we_o]
set_property C_CLK_INPUT_FREQ_HZ 300000000 [get_debug_cores dbg_hub]
set_property C_ENABLE_CLK_DIVIDER false [get_debug_cores dbg_hub]
set_property C_USER_SCAN_CHAIN 1 [get_debug_cores dbg_hub]
connect_debug_port dbg_hub/clk [get_nets clk]
