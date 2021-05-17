#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Helper script to invoke the Verible formatter with the proper
# configuration for OpenTitan.
#
# Arguments:
#
# --files|-f <file1> <file2> ...:
#   Run the formatter on individual files.
#
# --allowlist|-l:
#   Run the formatter on the files defined in
#   util/verible-format-allowlist.txt
#
# --all|-a:
#   Run the formatter on all *.sv and *.svh files in the tree.
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

# --allowlist and --all are run in the repo root
REPO_TOP=`git rev-parse --show-toplevel`

# select files to format
FILES_TO_FORMAT=""
while [ "$1" != "" ]; do
    case "$1" in
        --files|-f)
            shift 1
            while [ "$1" != "" ]; do
                FILES_TO_FORMAT="${FILES_TO_FORMAT}${1} "
                shift 1
            done
            ;;
        --allowlist|-l)
            cd $REPO_TOP
            FILES_TO_FORMAT=`grep -v '^#' util/verible-format-allowlist.txt`
            break
            ;;
        --all|-a)
            cd $REPO_TOP
            FILES_TO_FORMAT=`find . -type f -name "*.sv" -o -name "*.svh"`
            break
            ;;
        --*|-*)
            echo "Error: unsupported flag $1" >&2
            exit 1
            ;;
    esac
done

echo $FILES_TO_FORMAT | \
      xargs -n 1 -P $NUM_PROCS verible-verilog-format \
      $VERIBLE_ARGS
