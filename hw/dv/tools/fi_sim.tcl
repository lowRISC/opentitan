# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

if {[info exists ::env(FI_CAMPAIGN)]} {
  set fi_campaign "$::env(FI_CAMPAIGN)"
} else {
  puts "ERROR: FI_CAMPAIGN environment variable not set!"
  quit
}

if {[info exists ::env(FI_TC)]} {
  set fi_tc_name "$::env(FI_TC)"
} else {
  puts "ERROR: FI_TC environment variable not set!"
  quit
}

create_testcases -name $fi_tc_name -exec "$::env(SIMV)" -args "$::env(run_opts) +ntb_random_seed=$::env(seed) +UVM_TEST_SEQ=$::env(uvm_test_seq) -assert disable_assert" -fsim_args " -fsim=limit+hyperactive+0 -fsim=fault+monitor+drop"

# Currently hard coded to 2.
set_config -global_max_jobs 2

fsim

report -campaign $fi_campaign -report $::env(run_dir)/fsim_result.rpt -overwrite  -showfaultid

puts "TEST PASSED CHECKS"

fdb_disconnect
quit
