# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Variables that describe non-hermetic devices of the environment.

This repository provides 1 variable:
    - `CW_DEVICES`
        - The presence of ChipWhisperer devices (CW305, CW310, CW340).
"""

LIST_FPGA_SCRIPT = """
function _list_writable_usb() {(
    set -euo pipefail
    while read path; do
      bus=$(echo $path | cut -d/ -f5)
      dev=$(echo $path | cut -d/ -f6)
      lsusb -d 2b3e: -s $bus:$dev || true
    done <<< "$(find /dev/bus/usb -writable -type c)"
)}

function list_fpga() {(
    set -euo pipefail

    # Try lsusb with writable checks.
    if _list_writable_usb 2>/dev/null | grep -oE "CW3(05|10|40)" | sort -u; then
      return
    fi
    # Try udev symlinks.
    if ls /dev/serial/by-id/ 2>/dev/null | grep -oE "CW3(05|10|40)" | sort -u; then
      return
    fi
    # Fallback to lsusb
    lsusb -d 2b3e: | grep -oE "CW3(05|10|40)" | sort -u || true
)}
"""

def _devices_repo_impl(rctx):
    # List available USB devices with lsusb and filter for 'ChipWhisperer' (VID 2b3e)
    res = rctx.execute(["bash", "-c", """
      set -euo pipefail
      {LIST_FPGA_SCRIPT}
      list_fpga
    """.format(LIST_FPGA_SCRIPT = LIST_FPGA_SCRIPT)])
    cw_devices = res.stdout.strip()
    if cw_devices:
        print("Found ChipWhisperer:", cw_devices.split("\n"))
    else:
        print("No ChipWhisperer devices found.")

    rctx.file("devices.bzl", "CW_DEVICES = \"\"\"{}\"\"\"\n".format(cw_devices))
    rctx.file("BUILD.bazel", "exports_files(glob([\"**\"]))\n")

devices_repo = repository_rule(
    implementation = _devices_repo_impl,
    attrs = {},
    local = True,
)
