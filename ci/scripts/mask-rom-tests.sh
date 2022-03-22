#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -e -x

# This doesn't install dependencies, but should otherwise behave the
# same as what CI would do on a pull request
DEFAULT="master"

# use tests from a condonedlist
TESTS=(
  "//sw/device/silicon_creator/lib:error_unittest"
  "//sw/device/silicon_creator/lib:epmp_unittest"
  "//sw/device/silicon_creator/lib:manifest_unittest"
  "//sw/device/silicon_creator/lib:sigverify_mod_exp_ibex_unittest"
  "//sw/device/silicon_creator/lib:log_unittest"
  "//sw/device/silicon_creator/lib:sigverify_unittest"
  "//sw/device/silicon_creator/lib:shutdown_unittest"
  "//sw/device/silicon_creator/lib/base:sec_mmio_unittest"
  "//sw/device/silicon_creator/lib/drivers:uart_unittest"
  "//sw/device/silicon_creator/lib/drivers:lifecycle_unittest"
  "//sw/device/silicon_creator/lib/drivers:flash_ctrl_unittest"
  "//sw/device/silicon_creator/lib/drivers:rstmgr_unittest"
  "//sw/device/silicon_creator/lib/drivers:keymgr_unittest"
  "//sw/device/silicon_creator/lib/drivers:watchdog_unittest"
  "//sw/device/silicon_creator/lib/drivers:otbn_unittest"
  "//sw/device/silicon_creator/lib/drivers:otp_unittest"
  "//sw/device/silicon_creator/lib/drivers:retention_sram_unittest"
  "//sw/device/silicon_creator/lib/drivers:pinmux_unittest"
  "//sw/device/silicon_creator/lib/drivers:hmac_unittest"
  "//sw/device/silicon_creator/lib/drivers:alert_unittest"
  "//sw/device/silicon_creator/mask_rom:boot_policy_unittest"
  "//sw/device/silicon_creator/mask_rom:sigverify_keys_unittest"
)

git config advice.detachedHead false

ORIGINAL_BRANCH_NAME=$(git rev-parse --abbrev-ref HEAD 2>/dev/null || echo "")
ORIGINAL_SHA=$(git rev-parse HEAD)

summarize_tests () {
  bazel test --keep_going --nobuild_tests_only -- ${TESTS[*]}\
    | grep '//'\
    | sed 's/ (cached) / / ; s/ in / / ; s/ [0-9]\+.[0-9]\+s// ; s/ \+/ /g' \
    | sort > "$1"
  return "${PIPESTATUS[0]}"
}

mkdir -p bazel-results

if summarize_tests bazel-results/newresult.txt
then
  exit 0
fi

git remote add upstream https://github.com/lowrisc/opentitan.git || true
git fetch upstream $DEFAULT

if [ "$(git merge-base HEAD upstream/$DEFAULT)" != "$(git rev-parse HEAD)" ]
then
  # If on a branch we want to compare to the merge-base with master
  git checkout "$(git merge-base HEAD upstream/$DEFAULT)"
else
  # If on master we want to compare to the last tested ancestor, but that's
  # fairly hard to review so let's leave that alone for now. We wouldn't act on
  # it anyway.
  echo "Test is failing but I can't compare it to a merge base because we're on upstream/$DEFAULT"
  cat bazel-results/newresult.txt
  exit 0
fi

summarize_tests bazel-results/oldresult.txt || true

{ diff bazel-results/oldresult.txt bazel-results/newresult.txt > bazel-results/result.diff ; diffreturn="$?" ; } || true
case $diffreturn in
  0)
    echo "Reran and compared a summary of the outputs and they matched so this was already broken."
    cat bazel-results/newresult.txt
    git switch "$ORIGINAL_BRANCH_NAME" || git checkout "$ORIGINAL_SHA"
    exit 0 ;;
  1)
    echo "I found a different result"
    cat bazel-results/result.diff
    # Fail if anything used to pass and doesn't anymore
    echo "We'll pass only if none of the tests stopped passing when compared to the merge base"
    if [[ $(grep "<.*PASSED" -c bazel-results/result.diff) != 0 ]]
    then
      exit 1
    else
      git switch "$ORIGINAL_BRANCH_NAME" || git checkout "$ORIGINAL_SHA"
      exit 0
    fi
    ;;
  *)
    echo "diff returned $diffreturn which indicates trouble comparing" ;
    echo "Old Result"
    cat bazel-results/oldresult.txt
    echo "New Result"
    cat bazel-results/newresult.txt
    exit $diffreturn ;;
esac

