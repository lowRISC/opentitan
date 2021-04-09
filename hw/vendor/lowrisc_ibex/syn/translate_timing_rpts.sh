#!/bin/bash

# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

./python/build_translated_names.py ibex_top ./$LR_SYNTH_OUT_DIR/generated ./$LR_SYNTH_OUT_DIR/reports/timing/*.csv.rpt

for file in ./$LR_SYNTH_OUT_DIR/reports/timing/*.csv.rpt; do
  ./python/translate_timing_csv.py $file ./$LR_SYNTH_OUT_DIR/generated
done

