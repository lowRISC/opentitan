# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# This file sets common message configurations for all JasperGold tcl files.

# Save debug effort to escalate the following error messages
# Error out on use of undeclared signals
set_message -error VERI-9030

# Error out when a parameter is defined twice for an instance
set_message -error VERI-1402

# Downgrade the enum cast error to warnings.
# For example: JasperGold will throw an error and terminate if design assign an int to an enum
# type.
set_message -warning VERI-1348

# Downgrade the following error to warning:
# Assert with local variable assignment in non supported position: Non negative environment.
# Used for pwrmgr's pwrmgr_clock_enables_sva_if.sv assertion.
set_message -warning EOBS012

# Downgrade the following error to warning:
# When two submodules are connected via a wire, there is no need to explicitly declare that wire in
# the top module.
set_message -warning VERI-9030

# Disabling warnings:
# We use parameter instead of localparam in packages to allow redefinition
# at elaboration time.
# Formal isunknown does not support non-constant.
# Formal will skip initial construct.

# "parameter declared inside package XXX shall be treated as localparam"
set_message -disable VERI-2418

# "system function call isunknown with non-constant argument is not synthesizable"
set_message -disable VERI-1796

# "initial construct ignored"
set_message -disable VERI-1060

set_prove_verbosity 4
