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
    "adc_ctrl": ["https://reports.opentitan.org/hw/ip/adc_ctrl/dv/2023.10.16_18.03.35/"],
    "aes": ["https://reports.opentitan.org/hw/ip/aes_masked/dv/2023.10.16_18.04.57/",
            "https://reports.opentitan.org/hw/ip/aes_unmasked/dv/2023.10.16_18.04.21/"],
    "alert_handler":
    [("https://reports.opentitan.org/hw/top_earlgrey/ip_autogen/alert_handler/dv/"
      "2023.10.16_18.37.53/")],
    "aon_timer": ["https://reports.opentitan.org/hw/ip/aon_timer/dv/2023.10.16_18.05.42/"],
    "clkmgr": ["https://reports.opentitan.org/hw/ip/clkmgr/dv/2023.10.16_18.06.50/"],
    "csrng": ["https://reports.opentitan.org/hw/ip/csrng/dv/2023.10.16_18.07.39/"],
    "edn": ["https://reports.opentitan.org/hw/ip/edn/dv/2023.10.16_18.08.30/"],
    "entropy_src": ["https://reports.opentitan.org/hw/ip/entropy_src/dv/2023.10.16_18.09.15/"],
    "flash_ctrl": ["https://reports.opentitan.org/hw/ip/flash_ctrl/dv/2023.10.16_18.10.58/"],
    "gpio": ["https://reports.opentitan.org/hw/ip/gpio/dv/2023.10.16_18.12.48/"],
    "hmac": ["https://reports.opentitan.org/hw/ip/hmac/dv/2023.10.16_18.13.24/"],
    "i2c": ["https://reports.opentitan.org/hw/ip/i2c/dv/2023.10.16_18.14.22/"],
    "keymgr": ["https://reports.opentitan.org/hw/ip/keymgr/dv/2023.10.16_18.15.42/"],
    "kmac": ["https://reports.opentitan.org/hw/ip/kmac_masked/dv/2023.10.16_18.17.06/",
             "https://reports.opentitan.org/hw/ip/kmac_unmasked/dv/2023.10.16_18.17.38/"],
    "lc_ctrl": ["https://reports.opentitan.org/hw/ip/lc_ctrl/dv/2023.10.16_18.18.27/"],
    "otbn": ["https://reports.opentitan.org/hw/ip/otbn/dv/uvm/2023.10.16_18.19.22/"],
    "otp_ctrl": ["https://reports.opentitan.org/hw/ip/otp_ctrl/dv/2023.10.16_18.20.46/"],
    "pattgen": ["https://reports.opentitan.org/hw/ip/pattgen/dv/2023.10.16_18.21.41/"],
    "prim_alert": ["https://reports.opentitan.org/hw/ip/prim/dv/prim_alert/2023.10.16_18.22.07/"],
    "prim_esc": ["https://reports.opentitan.org/hw/ip/prim/dv/prim_esc/2023.10.16_18.22.31/"],
    "prim_lfsr": ["https://reports.opentitan.org/hw/ip/prim/dv/prim_lfsr/2023.10.16_18.22.54/"],
    "prim_present":
    ["https://reports.opentitan.org/hw/ip/prim/dv/prim_present/2023.10.16_18.23.17/"],
    "prim_prince": ["https://reports.opentitan.org/hw/ip/prim/dv/prim_prince/2023.10.16_18.23.44/"],
    "pwm": ["https://reports.opentitan.org/hw/ip/pwm/dv/2023.10.16_18.24.16/"],
    "pwrmgr": ["https://reports.opentitan.org/ip_autogen/pwrmgr/dv/2023.10.16_18.39.21/"],
    "rom_ctrl": ["https://reports.opentitan.org/hw/ip/rom_ctrl/dv/2023.10.16_18.25.05/"],
    "rstmgr": ["https://reports.opentitan.org/hw/ip/rstmgr/dv/2023.10.16_18.26.28/"],
    "rstmgr_cnsty_chk":
    ["https://reports.opentitan.org/hw/ip/rstmgr/dv/rstmgr_cnsty_chk/2023.10.16_18.25.40/"],
    "rv_dm": ["https://reports.opentitan.org/hw/ip/rv_dm/dv/2023.10.16_18.27.26/"],
    "rv_timer": ["https://reports.opentitan.org/hw/ip/rv_timer/dv/2023.10.16_18.28.14/"],
    "spi_device": ["https://reports.opentitan.org/hw/ip/spi_device/dv/2023.10.16_18.30.21/"],
    "spi_host": ["https://reports.opentitan.org/hw/ip/spi_host/dv/2023.10.16_18.28.52/"],
    "sram_ctrl": ["https://reports.opentitan.org/hw/ip/sram_ctrl_main/dv/2023.10.16_18.31.42/",
                  "https://reports.opentitan.org/hw/ip/sram_ctrl_ret/dv/2023.10.16_18.32.44/"],
    "sysrst_ctrl": ["https://reports.opentitan.org/hw/ip/sysrst_ctrl/dv/2023.10.16_18.33.56/"],
    "tl_agent": ["https://reports.opentitan.org/hw/dv/sv/tl_agent/dv/2023.10.16_18.02.43/"],
    "uart": ["https://reports.opentitan.org/hw/ip/uart/dv/2023.10.16_18.34.58/"],
    "usbdev": ["https://reports.opentitan.org/hw/ip/usbdev/dv/2023.10.16_18.36.00/"],
    "xbar":
    ["https://reports.opentitan.org/hw/top_earlgrey/ip/xbar_main/dv/autogen/2023.10.16_18.40.38/",
     "https://reports.opentitan.org/hw/top_earlgrey/ip/xbar_peri/dv/autogen/2023.10.16_18.41.48/"],
    "rv_core_ibex": ["https://ibex.reports.lowrisc.org/opentitan/latest/"],
}


def parse_report(path: str) -> Tuple[int, int]:
    with urlopen(f'https://reports.opentitan.org{path}/latest/report.json') as response:
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
        ) = parse_report(block['report']) if block['report'] else (None, None)

        output[name] = block_output

    with open(output_file, 'w') as f:
        json.dump(output, f, indent='  ')


if __name__ == "__main__":
    main()
