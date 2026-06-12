#!/bin/bash
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Classify the files changed since the merge base with the target branch
# into categories that CI jobs use to decide whether they are relevant to
# the change.
#
# Usage: classify-changes.sh [tgt-branch [head]]
#
# tgt-branch is the pull request's target branch (usually "master"). When
# it is empty or omitted (push and merge queue events), every category is
# reported as changed so that all jobs run.
#
# head is the revision containing the changes and defaults to HEAD. Pass
# this when classifying a pull request that is not checked out, e.g. from
# a pull_request_target workflow where only the head's *data* has been
# fetched. This script never executes any content of head.
#
# One "<category>=true|false" line per category is written to
# $GITHUB_OUTPUT (and echoed to stdout). Categories:
#
#   docs_only       Every changed file is documentation. Used to skip jobs
#                   whose dependency closure is too broad for an inclusion
#                   list.
#   otbn            OTBN hardware or software changed.
#   docker          Inputs of the developer container changed.
#   qemu            The QEMU build or its Bazel integration changed.
#   airgapped       Inputs of the airgapped build preparation changed.
#   rtl             SystemVerilog sources or lint configuration changed.
#   hw              Hardware or tooling changed. Used to skip RTL-only
#                   pipelines (e.g. AscentLint) for pure software changes.
#   top_earlgrey    The change is relevant to the Earl Grey design, i.e.
#                   not contained in other tops' directories or in
#                   documentation.
#   top_darjeeling  As above, for Darjeeling.
#
# Please keep the pathspecs conservative: prefer marking too many
# categories as changed (jobs run unnecessarily) over missing a relevant
# change (jobs are skipped incorrectly).

set -e

emit() {
  echo "${1}=${2}"
  echo "${1}=${2}" >> "${GITHUB_OUTPUT:-/dev/null}"
}

categories=(otbn docker qemu airgapped rtl hw top_earlgrey top_darjeeling)

if [ -z "${1:-}" ]; then
  echo "No target branch given; treating all categories as changed."
  emit docs_only false
  for category in "${categories[@]}"; do
    emit "$category" true
  done
  exit 0
fi

head="${2:-HEAD}"

merge_base="$(git merge-base "origin/$1" "$head")" || {
  echo >&2 "Failed to find fork point for origin/$1."
  exit 1
}
echo "Classifying files changed since ${merge_base}:"
git diff --name-only "$merge_base" "$head"
echo

# True if any file changed since the merge base matches the given pathspecs.
matches() {
  ! git diff --quiet "$merge_base" "$head" -- "$@"
}

bool() {
  if "$@"; then echo true; else echo false; fi
}

# Build-system and CI paths that can affect the result of any job. Every
# inclusion-based category below lists these so that infrastructure changes
# run everything.
infra=(
  'MODULE.bazel'
  '.bazelrc'
  '.bazelversion'
  'bazelisk.sh'
  'rules/'
  'third_party/'
  'ci/'
  '.github/'
)

# Documentation paths that cannot affect any build or test result. Keep
# this list small: anything not listed here runs the full CI.
docs=(
  ':!doc/'
  ':!site/'
  ':!util/site/'
  ':!*.md'
  ':!COMMITTERS'
  ':!CLA'
)

# A change is documentation-only if every changed file matches an
# exclusion above.
emit docs_only "$(bool git diff --quiet "$merge_base" "$head" -- "${docs[@]}")"

emit otbn "$(bool matches \
  'hw/ip/otbn/' \
  'sw/otbn/' \
  "${infra[@]}")"

emit docker "$(bool matches \
  'util/container/' \
  'util/get-toolchain.py' \
  'apt-requirements.txt' \
  'python-requirements.txt' \
  "${infra[@]}")"

emit qemu "$(bool matches \
  'third_party/qemu/' \
  "${infra[@]}")"

emit airgapped "$(bool matches \
  'util/prep-bazel-airgapped-build.sh' \
  "${infra[@]}")"

emit rtl "$(bool matches \
  '*.sv' \
  '*.svh' \
  '*.vbl' \
  'hw/lint/' \
  "${infra[@]}")"

emit hw "$(bool matches \
  'hw/' \
  'util/' \
  "${infra[@]}")"

# A top is unaffected only when every change is contained in other tops'
# directories or in documentation. Shared code (hw/ip/, sw/, util/, ...)
# counts as relevant to every top.
emit top_earlgrey "$(bool matches \
  ':!hw/top_darjeeling/' \
  ':!hw/top_englishbreakfast/' \
  "${docs[@]}")"

emit top_darjeeling "$(bool matches \
  ':!hw/top_earlgrey/' \
  ':!hw/top_englishbreakfast/' \
  "${docs[@]}")"
