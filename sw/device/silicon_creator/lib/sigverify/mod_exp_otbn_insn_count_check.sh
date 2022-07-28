#!/bin/sh
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Usage: mod_exp_otbn_insn_count_check.sh COUNTS_FILE HEADER_FILE
#
# COUNTS_FILE: file including min/max instruction counts
# HEADER_FILE: header file that should contain matching counts

set -e

counts_file="$1"
header_file="$2"

# Get the minimum/maximum instruction counts from the `counts_file`.
min=$(grep "Minimum instruction count: " "${counts_file}" | sed -e "s/Minimum instruction count: //")
max=$(grep "Maximum instruction count: " "${counts_file}" | sed -e "s/Maximum instruction count: //")
echo "Expected minimum count: ${min}"
echo "Expected maximum count: ${max}"

echo "If this test fails, double check that the instruction count range above matches the one in ${header_file}."

# Check that these numbers match the ones in the header file.
grep "kModExpOtbnInsnCountMin = ${min}," "${header_file}"
grep "kModExpOtbnInsnCountMax = ${max}," "${header_file}"
