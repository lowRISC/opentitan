#!/bin/bash

# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Ascentlint report summary generation script.
#

REPORT_DIR=reports

#-------------------------------------------------------------------------
# print header
#-------------------------------------------------------------------------
printf "NUMBER OF LINT ERRORS PER BLOCK:\n\n"
format="%20s %10s %10s \n"
printf "${format}" "Block" "Errors" "Warnings"
echo "-------------------------------------------"

#-------------------------------------------------------------------------
# run lint and summarize results
#-------------------------------------------------------------------------

for report in ${REPORT_DIR}/*.rpt ; do

  # summarize results
  crash=`grep "Exiting with error status" "${report%.*}.log"`
  if [[ ! -z "$crash" ]]; then
    error_cnt="CRASH"
    warni_cnt="CRASH"
  else
    error_cnt=`grep "^E  " "${report%.*}.rpt" | wc -l`
    warni_cnt=`grep "^W  " "${report%.*}.rpt" | wc -l`
  fi
  printf "${format}" `basename "${report%.*}"` $error_cnt $warni_cnt
done

echo "-------------------------------------------"
echo "END SUMMARY"

#-------------------------------------------------------------------------
# generate detailed reports
#-------------------------------------------------------------------------
printf "\n\nLIST OF ERRORS (E) AND WARNINGS (W) FOR EACH BLOCK:"
for report in ${REPORT_DIR}/*.rpt ; do

  printf "\n\n`basename "${report%.*}"`\n"

  # grep for lint crashes and lint errors, and limit line length
  grep "^  ERR" -A 2 "${report%.*}.log" | cut -c -200
  grep "^E  "        "${report%.*}.rpt" | cut -c -200
  grep "^W  "        "${report%.*}.rpt" | cut -c -200

done
