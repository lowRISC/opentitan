#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -o errexit
set -o pipefail

# If we are on an air-gapped machine, we need to first ensure the toolchain has
# been unpacked from the repository cache.
if [[ -n ${BAZEL_CACHE} ]]; then
  BAZEL_CMD="bazel"
  ${BAZEL_CMD} fetch \
    --distdir=${BAZEL_DISTDIR} \
    --repository_cache=${BAZEL_CACHE} \
    @com_lowrisc_toolchain_rv32imc_compiler//...
else
  BAZEL_CMD="./bazelisk.sh"
  ${BAZEL_CMD} fetch @com_lowrisc_toolchain_rv32imc_compiler//...
fi

# Set environment variables for the RV32 linker and assembler.
export RV32_TOOL_LD=$(${BAZEL_CMD} query \
  'deps(@com_lowrisc_toolchain_rv32imc_compiler//:bin/riscv32-unknown-elf-ld)' \
  --output location | cut -f1 -d:)
export RV32_TOOL_AS=$(${BAZEL_CMD} query \
  'deps(@com_lowrisc_toolchain_rv32imc_compiler//:bin/riscv32-unknown-elf-as)' \
  --output location | cut -f1 -d:)
