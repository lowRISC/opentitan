#!/usr/bin/env bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

##
# Run a simple HTTP server to display the results for individual runs.
#

set -e

PORT=3080

if [ ! -f venv/configured ] ; then
    rm -rf venv
    python3 -m venv venv
    source venv/bin/activate
    pip install -r requirements.txt
    touch venv/configured
else
    source venv/bin/activate
fi

python3 -m http.server --directory reports/ $PORT &
