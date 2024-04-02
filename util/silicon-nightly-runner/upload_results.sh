#!/usr/bin/env bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
##
# Submit test results to the google sheets.
# If a report is not provided it scans the archive dir and uploads them all.
#

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

set -e

if [ -n "$1" ]; then
    echo "Uploading report $1"
    ${PYTHON:-python3} ./ot_test_parser.py --upload --filename "$1" --runner-id "$VARIANT"
else
    archive_dir="archive"
    dir_list=`ls -1 -X $archive_dir`
    for dir in $dir_list
    do
        report="${archive_dir}/${dir}/test.xml"
        echo "Uploading report $report"
        ${PYTHON:-python3} ./ot_test_parser.py --upload --filename "$report" --runner-id "$VARIANT"
        # Sleep is needed to not exceed the google API quota
        sleep 10
    done
fi
