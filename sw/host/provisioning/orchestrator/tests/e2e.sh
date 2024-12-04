#!/bin/bash
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -ex

cp sw/host/provisioning/orchestrator/src/orchestrator.zip $TEST_TMPDIR

ORCHESTRATOR_PATH=$TEST_TMPDIR/orchestrator.zip

unzip $ORCHESTRATOR_PATH \
  "runfiles/lowrisc_opentitan/*" \
  "runfiles/openocd/*" \
  -d $TEST_TMPDIR
  # TODO: uncomment this line when we add the extensions in
  # "runfiles/provisioning_exts/*" \

mkdir -p $TEST_TMPDIR/runfiles/lowrisc_opentitan/external
cp -r $TEST_TMPDIR/runfiles/openocd/ $TEST_TMPDIR/runfiles/lowrisc_opentitan/external/

PROVISIONING_EXT_RUNFILES=$TEST_TMPDIR/runfiles/provisioning_exts
[ -d "${PROVISION_EXT_RUNFILES}" ] && \
  ln -fs "${PROVISIONING_EXT_RUNFILES}" \
    $TEST_TMPDIR/runfiles/lowrisc_opentitan/external/provisioning_exts

# Run tool. The path to the --sku-config parameter is relative to the
# runfiles-dir.
$PYTHON ${ORCHESTRATOR_PATH} \
  --sku-config=sw/host/provisioning/orchestrator/configs/skus/emulation.hjson \
  --test-unlock-token="0x11111111_11111111_11111111_11111111" \
  --test-exit-token="0x22222222_22222222_22222222_22222222" \
  --fpga=hyper310 \
  --non-interactive \
  --runfiles-dir=$TEST_TMPDIR/runfiles/lowrisc_opentitan \
  --db-path=$TEST_TMPDIR/registry.sqlite
