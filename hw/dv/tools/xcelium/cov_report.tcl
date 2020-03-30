# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Generate reports for the merged coverage in HTML and text format.

# Set the input merged coverage database directory using the env var 'cov_merge_db_dir'.
# The supplied env var may have quotes or spaces that needs to be trimmed.
set cov_merge_db_dir [string trim $::env(cov_merge_db_dir) " \""]

# Set the output directory for the reports database using the env var 'cov_report_dir'.
# The supplied env var may have quotes or spaces that needs to be trimmed.
set cov_report_dir [string trim $::env(cov_report_dir) " \""]

# Set the DUT name.
set dut [string trim $::env(DUT_TOP)]
set dut_uc [string toupper $dut]
set dut_instance [string trim $::env(dut_instance)]

# Load the merged coverage database.
load -run $cov_merge_db_dir

# Generate the text reports (summary is sufficient).
report -out $cov_report_dir/cov_report.txt -summary -inst uvm_pkg $dut \
  -metrics all -cumulative on -local off -grading covered

# Generate the HTML reports.
report_metrics -out $cov_report_dir -title $dut_uc -overwrite \
  -detail -kind aggregate -metrics all -source on \
  -exclComments -assertionStatus -allAssertionCounters \
  -all -inst -extended true
