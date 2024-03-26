# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
# shellcheck shell=bash

add_license_banner() {
  local outfile="$1"
# REUSE-IgnoreStart
  local license_banner="# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0"
# REUSE-IgnoreEnd
  TMP=$(mktemp)
  echo -e "$license_banner" > "$TMP"
  cat "$outfile" >> "$TMP"
  cat "$TMP" > "$outfile"
  rm -f "$TMP"
}

add_autogen_banner() {
  local outfile="$1"
  local cmd="$2"
  local autogen_banner="# THIS FILE HAS BEEN GENERATED, DO NOT EDIT MANUALLY. COMMAND:
# $cmd"
  TMP=$(mktemp)
  echo -e "$autogen_banner" > "$TMP"
  cat "$outfile" >> "$TMP"
  cat "$TMP" > "$outfile"
  rm -f "$TMP"
}
