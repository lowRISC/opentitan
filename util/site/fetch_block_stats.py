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
    "adc_ctrl": ["https://reports.opentitan.org/hw/ip/adc_ctrl/dv/2023.07.19_14.39.36/"],
    "aes": ["https://reports.opentitan.org/hw/ip/aes_masked/dv/2023.07.19_14.40.42/",
            "https://reports.opentitan.org/hw/ip/aes_unmasked/dv/2023.07.19_14.40.09/"],
    "alert_handler":
    [("https://reports.opentitan.org/hw/top_earlgrey/ip_autogen/alert_handler/dv/"
      "2023.07.19_15.09.49/")],
    "aon_timer": ["https://reports.opentitan.org/hw/ip/aon_timer/dv/2023.07.19_14.41.24/"],
    "clkmgr": ["https://reports.opentitan.org/hw/ip/clkmgr/dv/2023.07.19_14.42.23/"],
    "csrng": ["https://reports.opentitan.org/hw/ip/csrng/dv/2023.07.19_14.42.57/"],
    "edn": ["https://reports.opentitan.org/hw/ip/edn/dv/2023.07.19_14.43.47/"],
    "entropy_src": ["https://reports.opentitan.org/hw/ip/entropy_src/dv/2023.07.19_14.44.18/"],
    "flash_ctrl": ["https://reports.opentitan.org/hw/ip/flash_ctrl/dv/2023.07.19_14.45.57/"],
    "gpio": ["https://reports.opentitan.org/hw/ip/gpio/dv/2023.07.19_14.47.12/"],
    "hmac": ["https://reports.opentitan.org/hw/ip/hmac/dv/2023.07.19_14.47.56/"],
    "i2c": ["https://reports.opentitan.org/hw/ip/i2c/dv/2023.07.19_14.48.44/"],
    "keymgr": ["https://reports.opentitan.org/hw/ip/keymgr/dv/2023.07.19_14.49.50/"],
    "kmac": ["https://reports.opentitan.org/hw/ip/kmac_masked/dv/2023.07.19_14.50.53/",
             "https://reports.opentitan.org/hw/ip/kmac_unmasked/dv/2023.07.19_14.51.52/"],
    "lc_ctrl": ["https://reports.opentitan.org/hw/ip/lc_ctrl/dv/2023.07.19_14.52.44/"],
    "otbn": ["https://reports.opentitan.org/hw/ip/otbn/dv/uvm/2023.07.19_14.53.26/"],
    "otp_ctrl": ["https://reports.opentitan.org/hw/ip/otp_ctrl/dv/2023.07.19_14.54.39/"],
    "pattgen": ["https://reports.opentitan.org/hw/ip/pattgen/dv/2023.07.19_14.55.10/"],
    "prim_alert": ["https://reports.opentitan.org/hw/ip/prim/dv/prim_alert/2023.07.19_14.55.33/"],
    "prim_esc": ["https://reports.opentitan.org/hw/ip/prim/dv/prim_esc/2023.07.19_14.55.57/"],
    "prim_lfsr": ["https://reports.opentitan.org/hw/ip/prim/dv/prim_lfsr/2023.07.19_14.56.20/"],
    "prim_present":
    ["https://reports.opentitan.org/hw/ip/prim/dv/prim_present/2023.07.19_14.56.43/"],
    "prim_prince": ["https://reports.opentitan.org/hw/ip/prim/dv/prim_prince/2023.07.19_14.57.10/"],
    "pwm": ["https://reports.opentitan.org/hw/ip/pwm/dv/2023.07.19_14.57.40/"],
    "pwrmgr": ["https://reports.opentitan.org/hw/ip/pwrmgr/dv/2023.07.19_14.58.32/"],
    "rom_ctrl": ["https://reports.opentitan.org/hw/ip/rom_ctrl/dv/2023.07.19_14.59.16/"],
    "rstmgr": ["https://reports.opentitan.org/hw/ip/rstmgr/dv/2023.07.19_15.00.29/"],
    "rstmgr_cnsty_chk":
    ["https://reports.opentitan.org/hw/ip/rstmgr/dv/rstmgr_cnsty_chk/2023.07.19_14.59.42/"],
    "rv_dm": ["https://reports.opentitan.org/hw/ip/rv_dm/dv/2023.07.19_15.01.15/"],
    "rv_timer": ["https://reports.opentitan.org/hw/ip/rv_timer/dv/2023.07.19_15.01.54/"],
    "spi_device": ["https://reports.opentitan.org/hw/ip/spi_device/dv/2023.07.19_15.03.52/"],
    "spi_host": ["https://reports.opentitan.org/hw/ip/spi_host/dv/2023.07.19_15.02.26/"],
    "sram_ctrl": ["https://reports.opentitan.org/hw/ip/sram_ctrl_main/dv/2023.07.19_15.04.44/",
                  "https://reports.opentitan.org/hw/ip/sram_ctrl_ret/dv/2023.07.19_15.05.33/"],
    "sysrst_ctrl": ["https://reports.opentitan.org/hw/ip/sysrst_ctrl/dv/2023.07.19_15.06.32/"],
    "tl_agent": ["https://reports.opentitan.org/hw/dv/sv/tl_agent/dv/2023.07.19_14.38.42/"],
    "uart": ["https://reports.opentitan.org/hw/ip/uart/dv/2023.07.19_15.07.19/"],
    "usbdev": ["https://reports.opentitan.org/hw/ip/usbdev/dv/2023.07.19_15.08.11/"],
    "xbar":
    ["https://reports.opentitan.org/hw/top_earlgrey/ip/xbar_main/dv/autogen/2023.07.19_15.10.53/",
     "https://reports.opentitan.org/hw/top_earlgrey/ip/xbar_peri/dv/autogen/2023.07.19_15.11.46/"],
    "rv_core_ibex": ["https://ibex.reports.lowrisc.org/opentitan/latest/"],
}


def parse_report(path: str) -> Tuple[int, int]:
    for v_list in block_level_urls.values():
        for v in v_list:
            if v.startswith(f"https://reports.opentitan.org{path}"):
                url = f"{v}report.json"
                break
    print(f"path = {path}", file=sys.stderr)
    print(f"url = {url}", file=sys.stderr)
    with urlopen(url) as response:
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
        block_output['href'] = block['href']
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
