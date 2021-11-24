# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Generic constraints file for simple testsynthesis flow

# note that we do not fix hold timing in this flow
set SETUP_CLOCK_UNCERTAINTY 0.5

#####################
# main clock        #
#####################
set MAIN_CLK_PIN clk_i
set MAIN_RST_PIN rst_ni
# set main clock to 125 MHz
set MAIN_TCK  8.0
set_ideal_network ${MAIN_CLK_PIN}
set_ideal_network ${MAIN_RST_PIN}
set_clock_uncertainty ${SETUP_CLOCK_UNCERTAINTY} ${MAIN_CLK_PIN}

# other timing constraint in ns
set IN_DEL    1.0
set OUT_DEL   1.0
set DELAY     ${MAIN_TCK}

create_clock ${MAIN_CLK_PIN} -period ${MAIN_TCK}

# in to out
set_max_delay ${DELAY} -from [all_inputs] -to [all_outputs]
# in to reg / reg to out
set_input_delay ${IN_DEL} [remove_from_collection [all_inputs] {${MAIN_CLK_PIN}}] -clock ${MAIN_CLK_PIN}
set_output_delay ${OUT_DEL}  [all_outputs] -clock ${MAIN_CLK_PIN}

#####################
# I/O drive/load    #
#####################

# attach load and drivers to IOs to get a more realistic estimate
set_driving_cell  -no_design_rule -lib_cell ${DRIVING_CELL} -pin ${DRIVING_CELL_PIN} [all_inputs]
set_load [load_of ${LOAD_CELL_LIB}/${LOAD_CELL}/${LOAD_CELL_PIN}] [all_outputs]

# set a nonzero critical range to be able to spot the violating paths better
# in the report
set_critical_range 0.5 ${DUT}

#####################
# Size Only Cells   #
#####################

set_size_only -all_instances [get_cells -h *u_size_only*] true
