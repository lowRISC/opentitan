#!/usr/bin/env python3

# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Checks for Bazel targets in sim DV cfg files.
"""

import argparse
import sys
import hjson
from enum import Enum
from pathlib import Path
from typing import List

from lib.bazel_query import BazelQueryRunner

# List of fake targets added to please the linker:
FAKE_TARGETS = [
    "@manufacturer_test_hooks//:example_test_sim_dv",
]


# Copied from hw/top_earlgrey/dv/env/chip_env_pkg.sv for the type definitions.
class SwType(Enum):
    ROM = 0  # Ibex SW - first stage boot ROM.
    TEST_SLOT_A = 1  # Ibex SW - test SW in (flash) slot A.
    TEST_SLOT_B = 2  # Ibex SW - test SW in (flash) slot B.
    OTBN = 3  # Otbn SW
    OTP = 4  # Customized OTP image
    DEBUG = 5  # Debug SW - injected into SRAM.


def check_sw_image(name: str, sw_image: str, valid_bazel_targets: List[str]) -> List[str]:
    """
    Check that a sw_image is valid.

    Parameters:
        name: Name of the test.
        sw_image: Value of "sw_images" to check.
        valid_bazel_targets: List of valid bazel targets.

    Returns: list of errors detected.
    """
    # The format is sw_image is target:type[:flags]...
    # where the target is a bazel name so it also contains a ':', for example:
    #     //sw/device/silicon_creator/rom/e2e:rom_e2e_shutdown_exception_c:1:new_rules
    #     //sw/device/silicon_creator/rom/e2e:empty_test_slot_b_corrupted:2:ot_flash_binary:signed:fake_ecdsa_prod_key_0
    # The type indicate whether it's a flash image, otp image, and so on.
    # The flags can be used for other purposes such as indicating if the DV
    # requires a signed image.
    #
    # See:
    # - hw/top_earlgrey/dv/env/chip_env_cfg.sv for the actual parsing code
    # - hw/dv/tools/dvsim/sim.mk for the makefile that copies files
    # - hw/top_earlgrey/dv/env/chip_env_pkg.sv for the type definitions.
    try:
        bazel_module, bazel_label, other = sw_image.split(':', 2)
        other = other.split(':')
    except ValueError:
        return [f"{name}: invalid sw_image '{sw_image}'"]
    img_type = int(other[0])
    # If the bazel target does not start with '//' or '@', then prepend '//'
    # because all targets in valid_bazel_targets use an absolute path.
    if not bazel_module.startswith('//') and not bazel_module.startswith('@'):
        bazel_module = '//' + bazel_module
    bazel_target = f'{bazel_module}:{bazel_label}'
    # If the type is not OTP or Debug, then add the sim_dv suffix.
    if SwType(img_type) not in [SwType.OTP, SwType.DEBUG]:
        bazel_target = f'{bazel_target}_sim_dv'

    if bazel_target not in valid_bazel_targets:
        return [f"{name}: non-existent target '{bazel_target}' in sw_image={sw_image}"]
    return []


def check_links(cfg_hjson: Path, valid_bazel_targets: List[str]) -> List[str]:
    """
    Check all sw_images links in a sim DV cfg hsjon file.

    Parameters:
        cfg_hjson: Path to the file to check.
        valid_bazel_targets: List of valid bazel targets.

    Returns: list of errors detected.
    """
    sim_cfg = hjson.load(cfg_hjson.open())
    if 'tests' not in sim_cfg:
        return ["{} looks invalid: there are no tests"]
        return False
    problems = []
    for test in sim_cfg['tests']:
        if 'name' not in test:
            problems.append("invalid test without name")
            continue
        sw_images = test.get('sw_images', [])
        for sw_image in sw_images:
            problems.extend(check_sw_image(test['name'], sw_image, valid_bazel_targets))
    return problems


def main():
    parser = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('cfg_hjson_file', type=str, nargs='+', help='sim DV cfg hsjon files')
    args = parser.parse_args()

    bazel = BazelQueryRunner()

    # Search for all targets in device software.
    valid_bazel_targets = set(bazel.query("//..."))
    valid_bazel_targets |= set(FAKE_TARGETS)
    print("{} sim_dv targets identified".format(len(valid_bazel_targets)))

    ok = True
    for f in args.cfg_hjson_file:
        problems = check_links(Path(f), valid_bazel_targets)
        if problems:
            ok = False
            print(f"Errors in {f}:")
            for msg in problems:
                print(f"- {msg}")

    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
