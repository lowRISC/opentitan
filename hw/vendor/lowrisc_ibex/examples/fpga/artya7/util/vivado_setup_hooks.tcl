# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Setup hook scripts, to be called at various stages during the build process
# See Xilinx UG 894 ("Using Tcl Scripting") for documentation.

# fusesoc-generated workroot containing the Vivado project file
set workroot [pwd]
set vlogparam_list [get_property generic [get_filesets sources_1]]
set FPGAPowerAnalysis [regexp {FPGAPowerAnalysis} $vlogparam_list]
if {$FPGAPowerAnalysis == 1} {
        set_property STEPS.WRITE_BITSTREAM.TCL.PRE "${workroot}/vivado_hook_write_bitstream_pre.tcl" [get_runs impl_1]
}
