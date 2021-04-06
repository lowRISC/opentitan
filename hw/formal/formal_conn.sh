#!/bin/bash

# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Script to run connectivity test using Jasper Gold
#
# Usage: To run connectivity test on system level modules, type
#   formal_conn -f top_earlgrey.csv
#
# More options:
# -top: which top_level module to run
# -p:  provide core file path
# -gui: run with GUI mode
# -cov: run coverage
# -f: path to the csv file
# -t: choose which formal tool to use, current only support jaspergold
#
# Example:
#   formal_conn -f {path_to_csv_file}
#

set -e

CORE_PATH=systems:top_earlgrey
REPO_PATH=$(readlink -f ../..)

export DUT_TOP="top_earlgrey"
gui="-batch -command exit"  # default Batch mode
tool="jg"
export COV=0
export CSV_PATH
export COMMON_MSG_TCL_PATH=$(readlink -f tools/jaspergold/jaspergold_common_message_process.tcl)

while [ "$1" != "" ]; do
  case "$1" in
    "-top")
      shift
      DUT_TOP=$1
      ;;
    "-p")
      shift
      CORE_PATH=$1
      ;;
    "-gui")
      gui=""
      echo "runnin in GUI mode"
      ;;
    "-cov")
      COV=1
      echo "enable coverage"
      ;;
    "-t")
      shift
      tool=$1
      echo "running in tool: $tool"
      ;;
    "-f")
      shift
      CSV_PATH=$1
      echo "csv path: $CSV_PATH"
      ;;
    *)
      echo "ERROR: no match found for input $1"
      exit 1
      ;;
  esac
  shift
done

echo "-------------------------------------------------------------------------"
echo "-- Generate file list using FuseSoC"
echo "-------------------------------------------------------------------------"
echo ""
echo "Top: $DUT_TOP"
echo ""

rm -Rf build jgproject
echo "core_file path: lowrisc:${CORE_PATH}"

fusesoc --cores-root ../.. run\
        --tool=icarus --target=default\
        --flag=fileset_top\
        --setup "lowrisc:${CORE_PATH}"

echo "-------------------------------------------------------------------------"
echo "-- Run JasperGold"
echo "-------------------------------------------------------------------------"

cd build/*${DUT_TOP}*/default-icarus

if [ "${tool}" == "jg" ]; then
    jg ${gui} \
      ${REPO_PATH}/hw/formal/tools/jaspergold/conn.tcl \
      -proj {REPO_PATH}/hw/formal/jgproject \
      -allow_unsupported_OS \
      | tee ${REPO_PATH}/hw/formal/jg_conn.log
else
 echo "ERROR: TOOL ${tool} not supported"
 exit 1
fi
cd -

echo "-------------------------------------------------------------------------"
echo "-- Done"
echo "-------------------------------------------------------------------------"
