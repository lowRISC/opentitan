# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Generic constraints file for GTECH testsynthesis flow

#####################
# Size Only Cells   #
#####################

# This is analogous to the size_only constraint when using real ASIC cells.
set_dont_touch [get_designs -h prim_generic_xor*]
set_dont_touch [get_designs -h prim_generic_buf*]
set_dont_touch [get_designs -h prim_generic_clock_buf*]
set_dont_touch [get_designs -h prim_generic_inv*]
set_dont_touch [get_designs -h prim_generic_clock_inv*]
set_dont_touch [get_designs -h prim_generic_clock_mux*]
set_dont_touch [get_designs -h prim_generic_flop*]
