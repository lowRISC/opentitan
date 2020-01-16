# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

source ./tcl/flow_utils.tcl

print_lr_synth_banner
print_yosys_banner

source ./tcl/lr_synth_flow_var_setup.tcl

yosys "read_liberty -lib $lr_synth_cell_library_path"
