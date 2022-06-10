#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import chipwhisperer as cw


def main():
    target = cw.target(None, cw.targets.CW310, slurp=False)
    print("Found CW310 with FW Version: " + target.fw_version_str)
    target.reset_sam3u()


if __name__ == "__main__":
    main()
