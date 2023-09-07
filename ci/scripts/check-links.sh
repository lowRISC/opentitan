#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Checks links between files.

set -e

# Remove file containing invalid UTF-8
rm -f sw/vendor/eembc_coremark/docs/html/index/General2.html

# Run Offline Link Check
ci/bazelisk.sh run @lychee//:lychee -- SUMMARY.md hw/ sw/ doc/ util/ \
    --offline --no-progress \
    --exclude-path sw/vendor \
    --exclude-path util/i2csvg/smbus/SMBus.md \
    --exclude-path hw/ip_templates/ \
    --exclude-path hw/dv/doc/dv_doc_template.md \
    --exclude-path doc/rust_for_c_devs.md \
    --exclude-path hw/top_earlgrey/ip/pinmux/doc/autogen/targets.md \
    || {
      echo -n "##vso[task.logissue type=error]"
      echo "Link Check failed."
      exit 1
    }
