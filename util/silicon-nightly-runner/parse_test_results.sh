#!/usr/bin/env bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
##
# Parse the test results and submit them to the google sheets.
#

USER=$(whoami)
BRANCH=${BRANCH:-earlgrey_es_sival}

extra_parameters=()
ESLABELS=$(ls -1 "/dev/esowner-$USER" | sort -n | paste -sd,)
extra_parameters+=(--output-add-property "ESLabel=$ESLABELS")
extra_parameters+=(--output-add-property "User=$USER")
if [[ "$SHA1" != '' ]] ; then
    extra_parameters+=(--output-add-property "GITSHA=$SHA1")
fi
extra_parameters+=(--output-add-hostname)
extra_parameters+=(--output-flattened)

set -e

VARIANT="${VARIANT:-}"

if [ ! -f venv/configured ] ; then
    rm -rf venv
    python3 -m venv venv
    source "venv/bin/activate"
    pip install -r requirements.txt
    touch venv/configured
else
    source "venv/bin/activate"
fi

datenow=$(date +%Y-%m-%d)

archive_dir="archive/${datenow}"
mkdir -p "$archive_dir"

reports_dir=reports
mkdir -p "$reports_dir"

output_xml="${archive_dir}/test.xml"

echo "++++ Parsing and uploading tests results"
${PYTHON:-python3} ./ot_test_parser.py --results-date "$(date +%Y-%m-%d)" \
                                       --parse \
                                       --upload \
                                       --filename "$output_xml" \
                                       --runner-id "$VARIANT" \
                                       "${extra_parameters[@]}" \
                                       "$@"
                                       