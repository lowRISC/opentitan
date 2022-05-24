#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# A shell script for building a python-requirements.txt file based on a
# directory of wheels that have been pre-downloaded.

set -e

WHEEL_DIR="./"
OUTPUT_FILE="sanitized_requirements.txt"

for wheel in $(ls -1 ${WHEEL_DIR}/*.whl); do
  wheel_basename=$(echo ${wheel} | tr '\n' '\0' | xargs -0 -n 1 basename)
  IFS='-' read -ra WHEEL_NAME_ARRAY <<< ${wheel_basename}
  PACKAGE_NAME=${WHEEL_NAME_ARRAY[0]}
  PACKAGE_VERSION=${WHEEL_NAME_ARRAY[1]}
  echo "${PACKAGE_NAME}==${PACKAGE_VERSION}" >> ${OUTPUT_FILE}
done
