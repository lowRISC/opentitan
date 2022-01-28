#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Sets VCS_PARALLEL_BUILDS depending upon the current UK time
#
# The following environment variables must be set
# UK_WORKING_TIME_START_H: Start of the UK working day in hours
# UK_WORKING_TIME_START_M: Start of the UK working day in minutes
# UK_WORKING_TIME_END_H: End of the UK working day in hours
# UK_WORKING_TIME_END_M: End of the UK working day in minutes
#
# VCS_PARALLEL_BUILDS_UK_WORKING_DAY: Value to set VCS_PARALLEL_BUILDS to when
# during UK working hours
# VCS_PARALLEL_BUILDS_UK_DOWNTIME: Value to set VCS_PARALLEL_BUILDS to when
# outside of UK working hours

UK_WORKING_TIME_START_MINUTES=$(( "$UK_WORKING_TIME_START_H * 60 + $UK_WORKING_TIME_START_M" ))
UK_WORKING_TIME_END_MINUTES=$(( "$UK_WORKING_TIME_END_H * 60 + $UK_WORKING_TIME_END_M" ))

MINUTES_PAST_MIDNIGHT=$(( $(TZ='Europe/London' date "+10#%H * 60 + 10#%M") ))

if (( $MINUTES_PAST_MIDNIGHT >= $UK_WORKING_TIME_START_MINUTES )) && (( $MINUTES_PAST_MIDNIGHT < $UK_WORKING_TIME_END_MINUTES )); then
  export VCS_PARALLEL_BUILDS=$VCS_PARALLEL_BUILDS_UK_WORKING_DAY
else
  export VCS_PARALLEL_BUILDS=$VCS_PARALLEL_BUILDS_UK_DOWNTIME
fi
