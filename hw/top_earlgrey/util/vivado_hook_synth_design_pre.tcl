# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Change the severity of some messages.

# Abort if the boot ROM init file cannot be found. This is normally just a critical warning
# which is easily overlooked. The bitstream can still be generated but is not functional.
set_msg_config -id {[Synth 8-4445]} -new_severity ERROR

# Abort upon inferring latches. This is normally just a warning. We want to avoid that
# code inferring latches ends up in the repo in the first place.
set_msg_config -id {[Synth 8-327]} -new_severity ERROR

# Abort if a create_clock command fails. This typically happens if anchor points for clock
# constraints inside the design change. The failure is normally just reported as a critical
# warning in batch mode which is easily overlooked. The design might still work but some clocks
# will be unconstrained which can lead to other problems later on.
set_msg_config -id {[Vivado 12-4739]} -new_severity ERROR

# Abort if pblock constraints lose their target cells. This can happen if hierarchies change and
# the constraint doesn't get updated.
set_msg_config -id {[Vivado 12-1433]} -new_severity ERROR

# Save the current 'in-memory' project as actual project.  This is required for some of the commands
# below, such as `get_fileset`.
save_project_as -force lowrisc_systems_chip_earlgrey_cw310_0.1

# Create ILA IP core.
set ila_xci_path [ \
  create_ip -name ila -vendor xilinx.com -library ip -version 6.2 -module_name ila_0 \
]

# Configure ILA.
set_property -dict [list \
  CONFIG.C_PROBE0_WIDTH {42} \
  CONFIG.C_DATA_DEPTH {4096} \
  CONFIG.C_EN_STRG_QUAL {1} \
  CONFIG.C_PROBE0_MU_CNT {2} \
  CONFIG.ALL_PROBE_SAME_MU_CNT {2}\
] [get_ips ila_0]

# Generate synthesis and implementation targets.
generate_target {instantiation_template} [get_files $ila_xci_path]
generate_target -force all [get_files $ila_xci_path]
config_ip_cache -export [get_ips -all ila_0]
export_ip_user_files -of_objects [get_files $ila_xci_path] -no_script -sync -force -quiet
create_ip_run [get_files -of_objects [get_fileset sources_1] $ila_xci_path]

# Synthesize ILA OOC ahead of Earlgrey synthesis.
launch_runs ila_0_synth_1 -jobs 12
wait_on_run ila_0_synth_1

# Create ILA IP core.
set ila_xci_path [ \
  create_ip -name ila -vendor xilinx.com -library ip -version 6.2 -module_name ila_1 \
]

# Configure ILA.
set_property -dict [list \
  CONFIG.C_PROBE0_WIDTH {28} \
  CONFIG.C_DATA_DEPTH {4096} \
  CONFIG.C_EN_STRG_QUAL {1} \
  CONFIG.C_PROBE0_MU_CNT {2} \
  CONFIG.ALL_PROBE_SAME_MU_CNT {2}\
] [get_ips ila_1]

# Generate synthesis and implementation targets.
generate_target {instantiation_template} [get_files $ila_xci_path]
generate_target -force all [get_files $ila_xci_path]
config_ip_cache -export [get_ips -all ila_1]
export_ip_user_files -of_objects [get_files $ila_xci_path] -no_script -sync -force -quiet
create_ip_run [get_files -of_objects [get_fileset sources_1] $ila_xci_path]

# Synthesize ILA OOC ahead of Earlgrey synthesis.
launch_runs ila_1_synth_1 -jobs 12
wait_on_run ila_1_synth_1
