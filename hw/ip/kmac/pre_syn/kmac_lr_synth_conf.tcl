# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# List of inputs and outputs.  Number is timing constraint expressed as a % of
# clock cycle, e.g.
#
# {instr_req_o 70.0}
#
# as an output means the instr_req_o output must be stable by 70% of total clock
# cycle
#
# {instr_gnt_i 30.0}
#
# as an input means the instr_gnt_i input will be stable by 30% of the total
# clock cycle

# These IO constraints are an educated guess, they effectively assume there's a
# bit of external logic on the inputs and outputs but not much before they reach
# a flop.
set lr_synth_outputs [list {*_o 70.0}]
set lr_synth_inputs [list {*_i 30.0}]

# Clock and reset IO names (at top-level)
set lr_synth_clk_input clk_i
set lr_synth_rst_input rst_ni

# Clock period in ps, this gives a 125 MHz clock. Using the nangate45 library
# the AES module can happily meet this on all paths with the
# lr_synth_abc_clk_uprate setting below. With a lower uprate timing may not be
# met.
set lr_synth_clk_period 8000.0

# Amount to subtract from clk period to give the clock period passed to ABC in
# the synth flow. ABC maps the design to the standard cell library and
# optimises paths for timing, better results are obtained by giving it a faster
# clock period so it optimises more.
set lr_synth_abc_clk_uprate 4000.0
