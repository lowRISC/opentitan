## Copyright lowRISC contributors (OpenTitan project).
## Licensed under the Apache License, Version 2.0, see LICENSE for details.
## SPDX-License-Identifier: Apache-2.0

## Synthesis constraints

# Prevent Vivado from combining these BRAMs, so the memories can be readily
# spliced with updatemem.
set_property KEEP_HIERARCHY TRUE [get_cells "top_earlgrey/u_flash_ctrl/u_eflash/u_flash/gen_generic.u_impl_generic/gen_prim_flash_banks[0].u_prim_flash_bank/gen_info_types[0].u_info_mem"]
set_property KEEP_HIERARCHY TRUE [get_cells "top_earlgrey/u_flash_ctrl/u_eflash/u_flash/gen_generic.u_impl_generic/gen_prim_flash_banks[0].u_prim_flash_bank/gen_info_types[1].u_info_mem"]
set_property KEEP_HIERARCHY TRUE [get_cells "top_earlgrey/u_flash_ctrl/u_eflash/u_flash/gen_generic.u_impl_generic/gen_prim_flash_banks[0].u_prim_flash_bank/gen_info_types[2].u_info_mem"]
set_property KEEP_HIERARCHY TRUE [get_cells "top_earlgrey/u_flash_ctrl/u_eflash/u_flash/gen_generic.u_impl_generic/gen_prim_flash_banks[1].u_prim_flash_bank/gen_info_types[0].u_info_mem"]
set_property KEEP_HIERARCHY TRUE [get_cells "top_earlgrey/u_flash_ctrl/u_eflash/u_flash/gen_generic.u_impl_generic/gen_prim_flash_banks[1].u_prim_flash_bank/gen_info_types[1].u_info_mem"]
set_property KEEP_HIERARCHY TRUE [get_cells "top_earlgrey/u_flash_ctrl/u_eflash/u_flash/gen_generic.u_impl_generic/gen_prim_flash_banks[1].u_prim_flash_bank/gen_info_types[2].u_info_mem"]
