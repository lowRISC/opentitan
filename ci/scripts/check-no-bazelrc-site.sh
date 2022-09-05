#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Checks that .bazelrc-site file has not been accidentally committed to git
# where it could potentially impact the local configuration of other users.
#
# To be run in a CI environment (with a repo), and thus we simply check for
# the non-existence of the file, to confirm that it is not in the repo.

set -e

if [ -f .bazelrc-site ]; then
    echo -n "##vso[task.logissue type=error]"
    echo "The .bazelrc-site file should not appear in a clean checkout"
    exit 1
fi
