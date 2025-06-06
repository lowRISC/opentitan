#!/usr/bin/env bash

# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -e

REPO_TOP="$(git rev-parse --show-toplevel)"

cd "$REPO_TOP"

fail() {
  file="$1"
  command="$2"

  echo "::error::${file} is not up to date"             >&2
  echo "Regenerate this lock file using \`${command}\`" >&2

  exit 1
}

# Regenerate `MODULE.bazel.lock` file.
./bazelisk.sh mod deps
if ! git diff --exit-code MODULE.bazel.lock; then
  fail MODULE.bazel.lock "./bazelisk.sh mod deps"
fi

# Regenerate `Cargo.lock` files.
# We use the Cargo from Bazel to ensure there are no resolver version differences.
cargo=(bazel run @rules_rust//tools/upstream_wrapper:cargo --)
cargo_manifests=(
  third_party/rust/Cargo.toml
  third_party/tock/Cargo.toml
  third_party/mdbook/Cargo.toml
)
for toml in "${cargo_manifests[@]}"; do
  "${cargo[@]}" update -w --manifest-path "$toml"
  if ! git diff --exit-code "${toml/toml/lock}"; then
    fail "${toml/toml/lock}" "${cargo[*]} update -w --manifest-path ${toml}"
  fi
done

# Regenerate python lock file.
./util/sh/scripts/gen-python-requirements.sh
if ! git diff --exit-code python-requirements.txt; then
  fail python-requirements.txt ./util/sh/scripts/gen-python-requirements.txt
fi
