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
