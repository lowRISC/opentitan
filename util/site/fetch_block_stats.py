#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Fetches stats for the hw blocks and bundles them into a json file.

This script fetches the hw block data the diagram needs
and bundles it into one json file.
"""
from urllib.request import urlopen
from urllib.error import HTTPError
import itertools as it
import json
from pathlib import Path
import sys
from typing import Tuple

import hjson  # type: ignore

REPO_TOP = Path(__file__).parents[2].resolve()

block_level_urls = {
    "adc-controller": "hw/ip/adc_ctrl/dv/latest/",
    "aes": "hw/ip/aes_masked/dv/latest/",
    "alert-handler": "hw/top_earlgrey/ip_autogen/alert_handler/dv/latest/",
    "aon-timers": "hw/ip/aon_timer/dv/latest/",
    "clkrst-managers": "hw/top_earlgrey/ip_autogen/clkmgr/dv/latest/",
    "csrng": "hw/ip/csrng/dv/latest/",
    "edn": "hw/ip/edn/dv/latest/",
    "entropy-source": "hw/ip/entropy_src/dv/latest/",
    "flash": "hw/top_earlgrey/ip_autogen/flash_ctrl/dv/latest/",
    "gpio": "hw/top_earlgrey/ip_autogen/gpio/dv/latest/",
    "hmac": "hw/ip/hmac/dv/latest/",
    "i2c": "hw/ip/i2c/dv/latest/",
    "key-manager": "hw/ip/keymgr/dv/latest/",
    "kmac": "hw/ip/kmac_masked/dv/latest/",
    "life-cycle": "hw/ip/lc_ctrl/dv/latest/",
    "otbn": "hw/ip/otbn/dv/uvm/latest/",
    "otp-fuse-controller": "hw/top_earlgrey/ip_autogen/otp_ctrl/dv/latest/",
    "pattern-generators": "hw/ip/pattgen/dv/latest/",
    "pwm": "hw/top_earlgrey/ip_autogen/pwm/dv/latest/",
    "power-manager": "hw/top_earlgrey/ip_autogen/pwrmgr/dv/latest/",
    "rom": "hw/ip/rom_ctrl/dv/latest/",
    "debug-module": "hw/ip/rv_dm/dv/latest/",
    "timers": "hw/ip/rv_timer/dv/latest/",
    "spi-device": "hw/ip/spi_device/dv/latest/",
    "spi-host-0": "hw/ip/spi_host/dv/latest/",
    "spi-host-1": "hw/ip/spi_host/dv/latest/",
    "main-sram": "hw/ip/sram_ctrl_main/dv/latest/",
    "retention-sram": "hw/ip/sram_ctrl_ret/dv/latest/",
    "sysrst-controller": "hw/ip/sysrst_ctrl/dv/latest/",
    "uart": "hw/ip/uart/dv/latest/",
    "usb": "hw/ip/usbdev/dv/latest/",
    "high-speed-crossbar": "hw/top_earlgrey/ip/xbar_main/dv/autogen/latest/",
    "peripheral-crossbar": "hw/top_earlgrey/ip/xbar_peri/dv/autogen/latest/",
    "ibex": "https://ibex.reports.lowrisc.org/opentitan/latest/report.json",
}


def parse_report(url: str) -> Tuple[int, int]:
    try:
        with urlopen(url) as response:
            report = json.load(response)
    except HTTPError:
        # URL does not exist, there are no test runs yet for that
        return (0, 0)

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

        if name in block_level_urls:
            report_url = block_level_urls[name]
            if not report_url.startswith("https://"):
                report_url = f'https://reports.opentitan.org/{report_url}/report.json'
            (
                block_output['total_runs'],
                block_output['total_passing'],
            ) = parse_report(report_url)
        else:
            block_output['total_runs'] = None
            block_output['total_passing'] = None

        output[name] = block_output

    with open(output_file, 'w') as f:
        json.dump(output, f, indent='  ')


if __name__ == "__main__":
    main()
