#!/usr/bin/env bash

# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -e -o pipefail

trace_log="$(mktemp)"
trap 'rm ${trace_log}' EXIT

"$VERILATOR_SIM" --load_elf "$SMOKE_TEST_ELF" -t | tee "$trace_log"

grep -A 74 "Call Stack:" "$trace_log" | diff -U3 "$SMOKE_EXPECTED" - || had_diff=1

if [ "$had_diff" == 0 ]; then
  echo "OTBN SMOKE PASS"
else
  echo "Simulator output does not match expected output" >&2
  exit 1
fi
