#!/bin/bash
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Checks links between files.

set -e

# Run Offline Link Check.
#
# `--exclude-path sw/vendor` is load-bearing beyond skipping vendored docs:
# sw/vendor/eembc_coremark/docs/html/index/General2.html is not valid UTF-8
# (it comes from upstream that way), and lychee errors out on any input it
# cannot decode. Keep vendored code out of the input set rather than deleting
# the file: this is a check, and deleting it dirties the working tree by a
# local run of this script.
./bazelisk.sh run @lychee//:lychee -- SUMMARY.md hw/ sw/ doc/ util/ \
    --offline --no-progress \
    --exclude-path sw/vendor \
    --exclude-path util/i2csvg/smbus/SMBus.md \
    --exclude-path hw/ip_templates/ \
    --exclude-path hw/dv/doc/dv_doc_template.md \
    --exclude-path doc/rust_for_c_devs.md \
    --exclude-path hw/top_earlgrey/ip/pinmux/doc/autogen/targets.md ||
    {
        echo -n "::error::"
        echo "Link Check failed."
        exit 1
    }
