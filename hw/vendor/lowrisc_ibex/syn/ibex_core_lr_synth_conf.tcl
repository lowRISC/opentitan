# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# List of inputs and outputs.  Number is timing constraint expressed as a % of
# clock cycle, e.g.
#
# {instr_req_o 70.0}
#
# as an output means the instr_req_o output must be stable by 60% of total clock
# cycle
#
# {instr_gnt_i 30.0}
#
# as an input means the instr_gnt_i input will be stable by 30% of the total
# clock cycle

# These IO constraints are an educated guess, they effectively assume there's a
# bit of external logic on the inputs and outputs but not much before they reach
# a flop.
set lr_synth_outputs [list {instr_req_o   70.0} \
                           {instr_addr_o  70.0} \
                           {data_req_o    70.0} \
                           {data_we_o     70.0} \
                           {data_be_o     70.0} \
                           {data_addr_o   70.0} \
                           {data_wdata_o  70.0} \
                           {core_sleep_o  80.0}]

set lr_synth_inputs [list {test_en_i      0.0 } \
                          {hart_id_i      0.0 } \
                          {boot_addr_i    0.0 } \
                          {instr_gnt_i    30.0} \
                          {instr_rvalid_i 30.0} \
                          {instr_rdata_i  30.0} \
                          {instr_err_i    30.0} \
                          {data_gnt_i     30.0} \
                          {data_rvalid_i  30.0} \
                          {data_rdata_i   30.0} \
                          {data_err_i     30.0} \
                          {irq_software_i 10.0} \
                          {irq_timer_i    10.0} \
                          {irq_external_i 10.0} \
                          {irq_fast_i     10.0} \
                          {irq_nm_i       10.0} \
                          {debug_req_i    10.0} \
                          {fetch_enable_i 0.0 }]

# clock and reset IO names (at top-level)
set lr_synth_clk_input clk_i
set lr_synth_rst_input rst_ni

# clock period in ps, this gives a 250 MHz clock.  using the nangate45 library
# Ibex can happily meet this on all paths with the lr_synth_abc_clk_uprate
# setting below. With a lower uprate timing may not be met.
set lr_synth_clk_period 4000.0

# Amount to subtract from clk period to give the clock period passed to ABC in
# the synth flow. ABC maps the design to the standard cell library and
# optimises paths for timing, better results are obtained by giving it a faster
# clock period so it optimises more.
set lr_synth_abc_clk_uprate 2000.0
