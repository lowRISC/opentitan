#!/bin/bash
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -euo pipefail
source sw/host/hsmtool/tests/test_lib.sh

OPENTITANTOOL=sw/host/opentitantool/opentitantool

run ${OPENTITANTOOL} image digest \
  --bin image.digest ${IMAGE_BIN}

echo "Opentitantool calculated digest:"
basenc --base16 image.digest
echo "Known digest (calculated externally with sha256sum):"
basenc --base16 ${KNOWN_DIGEST}

run cmp image.digest ${KNOWN_DIGEST}
