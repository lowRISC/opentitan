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
# -gui: run with GUI
# -cov: run coverage
# -f: path to the csv file
# -t: choose which formal tool to use, current only support jaspergold
#
# Example:
#   formal_conn -gui -cov -f top_earlgrey_conn.csv
#

export TOP="top_earlgrey"
gui=0
tool="jg"
export COV=0
export CSV_PATH

while [ "$1" != "" ]; do
  case "$1" in
    "-top")
      shift
      TOP=$1
      ;;
    "-p")
      shift
      CORE_PATH=$1
      ;;
    "-gui")
      gui=1
      echo "using GUI mode"
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
      CSV_PATH=../../../../top_earlgrey/fpv/conn_csvs/$1
      echo "csv path: $CSV_PATH"
      ;;
  esac
  shift
done

echo "-------------------------------------------------------------------------"
echo "-- Generate file list using FuseSoC"
echo "-------------------------------------------------------------------------"
echo ""
echo "Top: $TOP"
echo ""

\rm -Rf build jgproject
# we just run the setup for the default target in order to generate the filelist
if [ "${CORE_PATH}" == "" ]; then
  CORE_PATH=systems:top_earlgrey
fi
echo "core_file path: lowrisc:${CORE_PATH}"

fusesoc --cores-root ../.. run\
        --tool=icarus --target=default\
        --flag=fileset_top\
        --setup "lowrisc:${CORE_PATH}"

echo "-------------------------------------------------------------------------"
echo "-- Run JasperGold"
echo "-------------------------------------------------------------------------"

cd build/*${TOP}*/default-icarus

if [ "${tool}" == "jg" ]; then
  if [ "${gui}" == "1" ]; then
    jg ../../../tools/jaspergold/conn.tcl \
       -proj ../../../jgproject \
       -allow_unsupported_OS \
       | tee ../../../jg_conn.log
  else
    jg -batch \
      ../../../tools/jaspergold/conn.tcl \
      -proj ../../../jgproject \
      -allow_unsupported_OS \
      -command exit \
      | tee ../../../jg_conn.log
  fi
else
 echo "-- ERROR: TOOL ${tool} not supported"
fi
cd -

echo "-------------------------------------------------------------------------"
echo "-- Done"
echo "-------------------------------------------------------------------------"
