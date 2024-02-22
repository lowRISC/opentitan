#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Fetches stats for the hw blocks and bundles them into a json file.

This script fetches the hw block data the diagram needs
and bundles it into one json file.
"""
from urllib.request import urlopen
import itertools as it
import json
from pathlib import Path
import sys
from typing import Tuple

import hjson  # type: ignore

REPO_TOP = Path(__file__).parents[2].resolve()

block_level_urls = {
    "adc-controller": "hw/ip/adc_ctrl/dv/2024.02.19_06.03.32/",
    "aes": "hw/ip/aes_masked/dv/2024.02.19_06.04.36/",
    "alert-handler": "hw/top_earlgrey/ip_autogen/alert_handler/dv/2024.02.19_06.17.59/",
    "aon-timers": "hw/ip/aon_timer/dv/2024.02.19_06.04.50/",
    "clkrst-managers": "hw/ip/clkmgr/dv/2024.02.19_06.05.08/",
    "csrng": "hw/ip/csrng/dv/2024.02.19_06.05.46/",
    "edn": "hw/ip/edn/dv/2024.02.19_06.06.01/",
    "entropy-source": "hw/ip/entropy_src/dv/2024.02.08_09.00.50/",
    "flash": "hw/ip/flash_ctrl/dv/2024.02.19_06.06.48/",
    "gpio": "hw/ip/gpio/dv/2024.02.19_06.07.30/",
    "hmac": "hw/ip/hmac/dv/2024.02.19_06.08.01/",
    "i2c": "hw/ip/i2c/dv/2024.02.19_06.08.19/",
    "key-manager": "hw/ip/keymgr/dv/2024.02.19_06.08.41/",
    "kmac": "hw/ip/kmac_masked/dv/2024.02.19_06.09.08/",
    "life-cycle": "hw/ip/lc_ctrl/dv/2024.02.19_06.09.58/",
    "otbn": "hw/ip/otbn/dv/uvm/2024.02.19_06.11.34",
    "otp-fuse-controller": "hw/ip/otp_ctrl/dv/2024.02.19_06.11.52/",
    "pattern-generators": "hw/ip/pattgen/dv/2024.02.19_06.12.37/",
    "pwm": "hw/ip/pwm/dv/2024.02.19_06.14.01/",
    "power-manager": "hw/top_earlgrey/ip_autogen/pwrmgr/dv/2024.02.19_06.18.39/",
    "rom": "hw/ip/rom_ctrl/dv/2024.02.19_06.14.14/",
    "debug-module": "hw/ip/rv_dm/dv/2024.02.19_06.14.33/",
    "timers": "hw/ip/rv_timer/dv/2024.02.19_06.14.53/",
    "spi-device": "hw/ip/spi_device/dv/2024.02.19_06.15.36/",
    "spi-host-0": "hw/ip/spi_host/dv/2024.02.19_06.15.22/",
    "spi-host-1": "hw/ip/spi_host/dv/2024.02.19_06.15.22/",
    "main-sram": "hw/ip/sram_ctrl_main/dv/2024.02.19_06.16.11/",
    "retention-sram": "hw/ip/sram_ctrl_ret/dv/2024.02.19_06.16.32/",
    "sysrst-controller": "hw/ip/sysrst_ctrl/dv/2024.02.19_06.16.53/",
    "uart": "hw/ip/uart/dv/2024.02.19_06.17.18/",
    "usb": "hw/ip/usbdev/dv/2024.02.19_06.17.38/",
    "high-speed-crossbar": "hw/top_earlgrey/ip/xbar_main/dv/autogen/2024.02.19_06.19.32/",
    "peripheral-crossbar": "hw/top_earlgrey/ip/xbar_peri/dv/autogen/2024.02.19_06.19.57/",
    "ibex": "https://ibex.reports.lowrisc.org/opentitan/latest",
}


def parse_report(path: str) -> Tuple[int, int]:
    print(f'Opening https://reports.opentitan.org/{path}/report.json')

    with urlopen(f'https://reports.opentitan.org/{path}/report.json') as response:
        report = json.load(response)

    # Extract all tests from the report.
    testpoints = report['results']['testpoints']
    tests_gen = it.chain(
        (test for testpoint in testpoints for test in testpoint['tests']),
        report['results']['unmapped_tests'],
    )
    # Convert into a dictionary to remove duplicates.
    tests = {test['name']: test for test in tests_gen}

    total_runs = sum(test['total_runs'] for test in tests.values())
    total_passing = sum(test['passing_runs'] for test in tests.values())

    return (total_runs, total_passing)


def parse_data_file(rel_path: str) -> Tuple[str, str, str]:
    with (REPO_TOP / rel_path).open() as f:
        block_data = hjson.load(f)

    try:
        return (
            block_data['version'],
            block_data['design_stage'],
            block_data['verification_stage'],
        )
    except KeyError:
        # Assumes the last value is the most recent
        revision = block_data['revisions'][-1]
        return (
            revision['version'],
            revision['design_stage'],
            revision['verification_stage'],
        )


def main() -> None:
    if len(sys.argv) < 2:
        prog = sys.argv[0]
        print(f"Usage: {prog} [output file]\nPlease provide an output file.")
        exit(1)

    output_file = sys.argv[1]

    blocks_file = Path(__file__).parent / "blocks.json"
    with blocks_file.open() as f:
        blocks = json.load(f)

    output = {}
    for (name, block) in blocks.items():
        print(f"fetching data for {name}")

        block_output = {}
        block_output['name'] = block['name']
        (
            block_output['version'],
            block_output['design_stage'],
            block_output['verification_stage'],
        ) = parse_data_file(block['data_file']) if block['data_file'] else (None, None, None)
        (
            block_output['total_runs'],
            block_output['total_passing'],
        ) = parse_report(block_level_urls[name]) if block['report'] else (None, None)

        output[name] = block_output

    with open(output_file, 'w') as f:
        json.dump(output, f, indent='  ')


if __name__ == "__main__":
    main()
