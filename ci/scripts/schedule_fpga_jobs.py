#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import json
from pathlib import Path
import subprocess
import sys
import json

class TestDatabase:
    def __init__(self, explain: bool):
        # Tests organized in a hashmap keyed by the test suite.
        self.tests_by_suite = dict()
        self.explain = explain

    def add_test(self, query_output_line):
        """
        Add a test to the database by parsing the output line of the
        cquery using ci/scripts/test_info_json.cquery
        """
        info = json.loads(query_output_line)
        # Ignore incompatible tests, or tests where the query could not extract
        # information
        if info.get('incompatible', False) or 'error' in info:
            if self.explain:
                print("{} ignored because it is not compatible".format(info["label"]))
            return
        # Ignore tests with certain tags
        BAD_TAGS = ["manual", "slow_test", "skip_in_ci", "broken"]
        if any(tag in info["tags"] for tag in BAD_TAGS):
            if self.explain:
                print("{} ignored because it contains a tag from {}".format(info["label"], BAD_TAGS))
            return

        if self.explain:
            print("{} added to the database".format(info))

        self.tests_by_suite.setdefault(info["test_suite"], []).append(info)

    def schedule_tests(self, filter_fn):
        """
        List all tests which match the filter function and return the list of
        their labels. Whenever a test is selected, it will be removed from the
        test suite to which it belongs and, unless the tests is marked with
        the `run_in_ci` tag, all the other tests which are not marked as `run_in_ci`
        will be removed from the suite.
        """
        selected_tests = []

        for (suite, tests) in self.tests_by_suite.items():
            discard_non_run_in_ci = False
            for test in tests:
                # Once we have schedule a non-run_in_ci job in the suite,
                # others non-run_in_ci are not elligible anymore.
                if ('run_in_ci' in test["tags"] or not discard_non_run_in_ci) and filter_fn(test):
                    selected_tests.append(test)
                    if self.explain:
                        print("{} was selected".format(test["label"]))
                    if 'run_in_ci' not in test["tags"]:
                        if self.explain:
                            print("  remaining non-run_in_ci tests in the suite " + suite +
                                  " will be discarded")
                        discard_non_run_in_ci = True
            # Update the test suite:
            new_tests = []
            selected_labels = set([t["label"] for t in selected_tests])
            for test in tests:
                # Do not keep selected tests.
                if test["label"] in selected_labels:
                    continue
                # If asked to, do not keep non-run_in_ci tests.
                if 'run_in_ci' in test["tags"] or not discard_non_run_in_ci:
                    new_tests.append(test)
                elif self.explain:
                    print("{} is non-run_in_ci and will be discarded".format(test["label"]))
            # Modify in place.
            tests.clear()
            tests.extend(new_tests)

        return selected_tests

FPGAS = {
    "cw340": {
        "human_name": "CW340",
        "ci_board": "cw340",
        "ci_bitstream": "chip_earlgrey_cw340",
        "ci_interface": "cw340",
    },
    "cw310": {
        "human_name": "CW310",
        "ci_board": "cw310",
        "ci_bitstream": "chip_earlgrey_cw310_hyperdebug",
        "ci_interface": "hyper310",
    }
}

JOBS = [
    {"name": "Manufacturing", "tags": ["manuf", "cw340"], "fpga": "cw340", "id": "manuf"},
    {"name": "Manufacturing", "tags": ["manuf", "cw310"], "fpga": "cw310", "id": "manuf"},
] + [
    {"name": target, "tags": [f"{fpga}_{tag}"], "fpga": fpga, "id": f"{tag}"}
    # Watch the order here!
    for (target, tag) in [("SiVal ROM_EXT", "sival_rom_ext"), ("SiVal", "sival"), ("ROM_EXT", "rom_ext")]
    for fpga in ["cw340", "cw310"]
] + [
    {"name": "ROM", "tags": ["cw340_rom_with_fake_keys"], "fpga": "cw340", "id": "rom"},
    {"name": "ROM", "tags": ["cw310_rom_with_fake_keys"], "fpga": "cw310", "id": "rom"},
    {"name": "TestROM", "tags": ["cw340_test_rom"], "fpga": "cw340", "id": "test_rom"},
    {"name": "TestROM", "tags": ["cw310_test_rom"], "fpga": "cw310", "id": "test_rom"},
]

# Average time it takes to run a test,
# assuming that the bitstream is already loaded.
AVERAGE_TEST_RUNTIME_SECS = 5
# Time it takes to load a bitstream, keyed by fpga.
BITSTREAM_LOAD_TIME_SECS = {
    'cw310': 10,
    'cw340': 20,
}
# Maximum job length in minutes.
MAX_JOB_LENGTH_MIN = 30

def estimated_test_runtime(fpga, test):
    """
    Return estimatd runtime in seconds.
    """
    # If the tag contains the `changes_otp` flag, then the bitstream will have to be cleared
    # at the end, so we count this in the running time of this test.
    load_time = BITSTREAM_LOAD_TIME_SECS[fpga] if 'changes_otp' in test['tags'] else 0
    return AVERAGE_TEST_RUNTIME_SECS + load_time


def split_job(fpga, tests, max_job_length_min):
    jobs = []
    cur_job = []
    cur_job_time = 0
    for test in tests:
        test_time = estimated_test_runtime(fpga, test)
        # If we go above the limit, commit current job and start a new one.
        if cur_job_time + test_time > max_job_length_min * 60:
            jobs.append(cur_job)
            cur_job = []
            cur_job_time = 0
        # Add test to current job
        cur_job.append(test)
        cur_job_time += test_time
    # Commit job if non-empty
    if cur_job:
        jobs.append(cur_job)
    return jobs


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--out-dir",
        required=True,
        type=Path,
        help="Output directory for the files",
    )
    parser.add_argument(
        "--explain",
        action="store_true",
        help="Explain scheduling decisions",
    )
    parser.add_argument(
        "query",
        default=['//...'],
        metavar="QUERY...",
        nargs='*',
        help="Arguments forwared to bazel cquery to list targets",
    )
    args = parser.parse_args()

    initial_args = [
        "./bazelisk.sh",
        "cquery",
        "--output=starlark",
        "--starlark:file=ci/scripts/test_info_json.cquery",
    ]

    res = subprocess.check_output(
        initial_args + args.query,
        text = True,
    )
    test_db = TestDatabase(args.explain)
    for line in res.splitlines():
        test_db.add_test(line)

    args.out_dir.mkdir(exist_ok = True)

    # Schedule all jobs.
    jobs = []
    for job in JOBS:
        fpga = FPGAS[job["fpga"]]
        tests = test_db.schedule_tests(lambda test: all(tag in test["tags"] for tag in job["tags"]))
        tests = split_job(job["fpga"], tests, MAX_JOB_LENGTH_MIN)
        for (part, job_tests) in enumerate(tests, start=1):
            suffix = "" if len(tests) == 1 else f"_{part}"
            id = "{}_{}{}".format(job["fpga"], job["id"], suffix)
            human_suffix = "" if len(tests) == 1 else " ({} / {})".format(part, len(tests))
            job_tests = [t["label"] for t in job_tests]
            (args.out_dir / f"{id}.txt").write_text("\n".join(job_tests))
            jobs.append({
                "name": "{} {} Tests{}".format(fpga["human_name"], job["name"], human_suffix),
                "board": fpga["ci_board"],
                "bitstream": fpga["ci_bitstream"],
                "interface": fpga["ci_interface"],
                "id": id,
                "target_file": f"{id}.txt",
            })
    # Make sure that there are no FPGA jobs left
    rem_fpga_tests = test_db.schedule_tests(lambda test: "fpga" in test["tags"])
    if rem_fpga_tests:
        print("Error: the following tests were not scheduled", file=sys.stderr)
        for test in rem_fpga_tests:
            print(test, file=sys.stderr)
        sys.exit(1)

    print(json.dumps(jobs, indent=4))


if __name__ == '__main__':
    sys.exit(main())
