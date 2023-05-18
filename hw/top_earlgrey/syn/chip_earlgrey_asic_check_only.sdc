# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# These SDC's are not used for synthesis, since they collide with the current
# set_clock_groups -async constraints. Instead, they are used to time the design
# after P&R in order to make sure that the CDC crossings are all within spec.
#
# Note that this script assumes that the clocks have been created and that their
# period is known.

#####################
# CDC               #
#####################

# Note that this does not include any SPI-specific clocks, since these
# paths are constrained separately.
set CDC_CONSTRAINT_CLOCKS { MAIN_CLK    \
                            USB_CLK     \
                            IO_CLK      \
                            IO_DIV2_CLK \
                            IO_DIV4_CLK \
                            JTAG_TCK    \
                            AON_CLK }

set CDC_CONSTRAINT_PERIODS { $MAIN_TCK_PERIOD    \
                             $USB_TCK_PERIOD     \
                             $IO_TCK_PERIOD      \
                             $IO_DIV2_TCK_PERIOD \
                             $IO_DIV4_TCK_PERIOD \
                             $JTAG_TCK_PERIOD    \
                             $AON_TCK_PERIOD }

# Generic CDC constraints, ensuring that all crossings have a maximum delay
# of 90% of the target clock period.
set idx 0
foreach THIS_CLOCK $CDC_CONSTRAINT_CLOCKS {
    set OTHER_CLOCKS [lreplace $CDC_CONSTRAINT_CLOCKS $idx $idx]
    set THIS_TCK_PERIOD [lindex $CDC_CONSTRAINT_PERIODS $idx]
    set CONSTRAINT [expr $THIS_TCK_PERIOD*0.9]
    set idx [expr $idx + 1]
    puts "setting set_max_delay -from $OTHER_CLOCKS -to $THIS_CLOCK $CONSTRAINT"
    set_max_delay -from $OTHER_CLOCKS -to $THIS_CLOCK $CONSTRAINT
}

# Although the alert channels should already be checked implicitly with the
# constraints above, we also add an explicit, stricter check here.
set MAX_DELAY [expr $MAIN_TCK_PERIOD * 0.9]
set_max_delay -to [get_pins -hierarchical -filter "full_name =~ *u_decode_ack/*i_sync_?/*u_sync_1*/D"] $MAX_DELAY
set_max_delay -to [get_pins -hierarchical -filter "full_name =~ *u_decode_alert/*i_sync_?/*u_sync_1*/D"] $MAX_DELAY
set_max_delay -to [get_pins -hierarchical -filter "full_name =~ *u_decode_ping/*i_sync_?/*u_sync_1*/D"] $MAX_DELAY

# Use a stricter constraint for FIFO gray pointers
set GRAY_MAX_DELAY [expr $MAIN_TCK_PERIOD * 0.5]

# For prim_fifo_async.sv (flop-based FIFO)
set_max_delay $GRAY_MAX_DELAY -to [get_pins -hierarchical -filter "full_name =~ */sync_wptr/u_sync_1/gen_*u_impl*/gen_flops?0?*?u_size_only_reg/D"]
set_max_delay $GRAY_MAX_DELAY -to [get_pins -hierarchical -filter "full_name =~ */sync_rptr/u_sync_1/gen_*u_impl*/gen_flops?0?*?u_size_only_reg/D"]

# For prim_fifo_async_sram_adapter.sv (no data array. this is an adapter that interfaces with a dual port SRAM)
set_max_delay $GRAY_MAX_DELAY -to [get_pins -hierarchical -filter "full_name =~ */u_sync_wptr_gray/u_sync_1/gen_*u_impl*/gen_flops?0?*?u_size_only_reg/D"]
set_max_delay $GRAY_MAX_DELAY -to [get_pins -hierarchical -filter "full_name =~ */u_sync_rptr_gray/u_sync_1/gen_*u_impl*/gen_flops?0?*?u_size_only_reg/D"]
