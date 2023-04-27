# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Post elab script, used in GTECH runs to modify the unmapped netlist before
# writing it out.

# Remove generic views of ram macros
remove_design prim_generic_ram_1p_Width*
remove_design prim_generic_ram_2p_Width*

