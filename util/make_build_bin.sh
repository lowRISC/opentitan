#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -e

# make_build_bin.sh takes the unstructured contents of $OBJ_DIR and copies them
# into the stable file structure of $BIN_DIR. By default, this script will skip
# any subdirectory of $OBJ_DIR unknown to it, but setting $MUST_COPY_ALL will
# cause trigger a hard error if any $OBJ_DIR subdir is missing.

. util/build_consts.sh

for platform in "${PLATFORMS[@]}"; do
  obj_dir="$(sw_obj_dir "$platform")"
  echo "Copying object directory $obj_dir."
  if [[ ! -d "$obj_dir" ]]; then
    if [[ -z ${MUST_COPY_ALL+x} ]]; then
      echo "Error: Object directory for $platform does not exist; skipping."
      continue
    else
      echo "Error: Object directory for $platform does not exist; aborting."
      exit 1
    fi
  fi

  bin_dir="$(sw_bin_dir "$platform")"
  # NOTE: This find excludes all directory paths with '@' symbols in them, which
  # are used by Meson to indicate unexported build artifacts, like .o and .a files.
  for path in $(find "$obj_dir/sw/device" -type f -regex '[^@]+'); do
    # NOTE: The '#' substitution operator strips the prefix $obj_root from $path.
    rel_dir="$(dirname "${path#"$obj_dir/sw/device/"}")"
    mkdir -p "$bin_dir/$rel_dir"
    cp "$path" "$bin_dir/$rel_dir"
  done

  # TODO: "Host" binaries must be copied separately. Currently, Meson will compile
  # them once per platform, even though they are the same for all platforms.
  # As such, we copy them from the first object directory we encounter.
  if [[ -z ${found_host_bins+x} ]]; then
    host_obj_dir="$obj_dir/sw/host"
    if [[ ! -d "$host_obj_dir" ]]; then
      continue
    fi
    echo "Copying host binaries from $host_obj_dir."
    for path in $(find "$host_obj_dir" -type f -regex '[^@]+'); do
      rel_dir="$(dirname "${path#$host_obj_dir}")"
      mkdir -p "$HOST_BIN_DIR/$rel_dir"
      cp "$path" "$HOST_BIN_DIR/$rel_dir"
    done
    found_host_bins=true
  fi
done
