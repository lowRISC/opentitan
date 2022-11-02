#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# A wrapper that duplicates the code for the quick lint job in
# azure-pipelines.yml. The two should be kept in sync.
#
# This doesn't install dependencies, but should otherwise behave the
# same as what CI would do on a pull request.

set -e

echo -e "\n### Check tags on Bazel artifacts"
ci/scripts/check-bazel-tags.sh

echo -e "\n### Ensure bazel doesn't use 'git_repository's"
ci/scripts/check-bazel-banned-rules.sh

echo -e "\n### Ensure all generated files are clean and up-to-date"
ci/scripts/check-generated.sh

echo -e "\n### Use buiildifier to check Bazel coding style"
bazel test //quality:buildifier_check --test_output=streamed

echo "### Check vendored directories are up-to-date"
ci/scripts/check-vendoring.sh

echo -e "\n### Style-Lint RTL Verilog source files with Verible"
ci/scripts/verible-lint.sh rtl

echo -e "\n### Style-Lint DV Verilog source files with Verible"
ci/scripts/verible-lint.sh dv

echo -e "\n### Style-Lint FPV Verilog source files with Verible"
ci/scripts/verible-lint.sh fpv
