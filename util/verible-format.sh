#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# this script runs the verible formatter on all system verilog
# files under hw/{ip,vendor,top_earlgrey}
#
# make sure to invoke this tool from the project root.
#
# NOTE: this operates in-place - so make sure to make a backup or
# run this on an experimental branch
#
# TODO: integrate this with Fusesoc and the other linting flows.

NUM_PROCS=8
REPORT_FILE="verible-format.rpt"
VERIBLE_VERSION=`verible-verilog-format --version`
VERIBLE_ARGS="--formal_parameters_indentation=indent \
              --named_parameter_indentation=indent   \
              --named_port_indentation=indent        \
              --port_declarations_indentation=indent \
              --inplace"

if [[ -z $VERIBLE_VERSION ]]; then
    echo "verible-verilog-format either not installed or not visible in PATH"
    exit 1
fi

# this is a precaution in order to prevent accidental
# overwriting of uncomitted changes
git add -u

# By default format only files in allow list
MODE=${MODE:-allowlist}

case $MODE in
    allowlist)
        FILES_TO_FORMAT=`grep -v '^#' util/verible-format-allowlist.txt`
        ;;

    all)
        # get all system verilog files and pipe through style formatter
        FILES_TO_FORMAT=`find . -type f -name "*.sv" -o -name "*.svh"`
        ;;

    *)
        echo "verible-format.sh: Unknown mode $MODE"
        exit 1
        ;;
esac

echo $FILES_TO_FORMAT | \
      xargs -n 1 -P $NUM_PROCS verible-verilog-format \
      $VERIBLE_ARGS


echo "Using verible-verilog-format version $VERIBLE_VERSION" > $REPORT_FILE

# report changed files
git status                  | \
    grep modified           | \
    grep dv                 | \
    awk -F ' ' '{print $2}' | \
    tee -a $REPORT_FILE
