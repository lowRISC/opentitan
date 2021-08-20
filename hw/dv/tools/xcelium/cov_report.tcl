# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Generate reports for the merged coverage in HTML and text format.
#
# This file is passed to IMC using the -exec switch. Ensure that the merged coverage database, the
# exclusion script and the coverage refinement files are passed to the IMC invocation using the
# -load, -init and -load_refinement switches respectively (whichever ones are applicable).

# Set the output directory for the reports database using the env var 'cov_report_dir'.
# The supplied env var may have quotes or spaces that needs to be trimmed.
set cov_report_dir [string trim $::env(cov_report_dir) " \"'"]

# Set the DUT name.
set dut [string trim $::env(DUT_TOP)]
set dut_uc [string toupper $dut]

# Generate the text report (summary is sufficient).
report -summary \
  -inst uvm_pkg $dut \
  -metrics all \
  -all \
  -cumulative on \
  -local off \
  -grading covered \
  -out $cov_report_dir/cov_report.txt

# Generate the functional coverage report for tracking.
report -summary \
  -type \
  -all \
  -metrics covergroup \
  -source off \
  -out $cov_report_dir/cov_report_cg.txt

# Generate the HTML reports.
report_metrics \
  -out $cov_report_dir \
  -overwrite \
  -title $dut_uc \
  -detail \
  -metrics all \
  -kind aggregate \
  -source on \
  -exclComments \
  -assertionStatus \
  -allAssertionCounters \
  -all
