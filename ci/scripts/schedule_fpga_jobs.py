#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""
Script to create a schedule of the FPGA jobs in CI using bazel queries.

This script uses the information contained in the OpenTitanTestInfo
providers to build a set of jobs for the various execution environments.
The script tries to estimate the maximum running time and ensure that jobs
do not take too long, splitting them into several jobs if necessary.
"""

import argparse
import json
from pathlib import Path
import subprocess
import sys
import tempfile

TEST_INFO_QUERY = """
# This query looks for test targets and print some information in json format.
# The output is a dictionary with the following keys:
# - label: the complete label of the target
# - compatible: boolean to indicate whether the target is compatible or not
# - test_suite: label of the test suite
# - tags: array of tags
# The test suite is determined using the OpenTitanTestInfo is present, and
# is set to itself otherwise.
def format(target):
    # Ignore incompatible targets
    info = {
        "label": str(target.label),
        "compatible": not "IncompatiblePlatformProvider" in providers(target),
    }
    ot_test_info = None
    for (provider_name, provider) in providers(target).items():
        if '//rules/opentitan:providers.bzl%OpenTitanTestInfo' in provider_name:
            ot_test_info = provider
    if ot_test_info:
        info["test_suite"] = ot_test_info.test_suite
        info["tags"] = ot_test_info.tags
    else:
        # If we could not find the provider, report the error.
        info["ignore"] = "No OpenTitanTestInfo provider found"
    return json.encode(info)
"""


class TestDatabase:
    def __init__(self, explain: bool, bad_tags: list[str], good_tags: list[str]):
        # Tests organized in a hashmap keyed by the test suite.
        self.tests_by_suite = dict()
        self.explain = explain
        self.bad_tags = bad_tags
        self.good_tags = good_tags

    def add_test(self, query_output_line):
        """
        Add a test to the database by parsing the output line of the cquery.
        """
        info = json.loads(query_output_line)
        label = info["label"]
        if self.explain:
            print(f"Considering {info}", file=sys.stderr)
        # Ignore incompatible tests.
        if not info.get('compatible', True):
            if self.explain:
                print(f"{label} ignored because it is not compatible", file=sys.stderr)
            return
        # Ignore targets which cannot be queried.
        if 'ignore' in info:
            if self.explain:
                print("{} ignored: {}".format(info["label"], info["ignore"]), file=sys.stderr)
            return
        # Ignore tests with certain tags.
        if any(tag in info["tags"] for tag in self.bad_tags):
            if self.explain:
                print(f"{label} ignored because it contains a negative filter tag", file=sys.stderr)
            return
        # Check if it contains at least one good tag.
        if self.good_tags and not any(tag in info["tags"] for tag in self.good_tags):
            if self.explain:
                print(f"{label} ignored because it does not match any positive filter tag",
                      file=sys.stderr)
            return

        if self.explain:
            print(f"{label} added to the database", file=sys.stderr)

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
                # Once we have scheduled a non-run_in_ci job in the suite,
                # others non-run_in_ci are not eligible anymore.
                if ('run_in_ci' in test["tags"] or not discard_non_run_in_ci) and filter_fn(test):
                    selected_tests.append(test)
                    if self.explain:
                        print("{} was selected".format(test["label"]), file=sys.stderr)
                    if 'run_in_ci' not in test["tags"]:
                        if self.explain:
                            print(f"  remaining non-run_in_ci tests in the suite {suite} will be discarded", file=sys.stderr)  # noqa: E501
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
        # Time it takes to load a bitstream, in seconds.
        "load_time": 20,
    },
    "cw310": {
        "human_name": "CW310",
        "ci_board": "cw310",
        "load_time": 10,
    }
}


def create_schedule(human_name: str, fpga: str, job_id: str, tests):
    fpga = FPGAS[fpga]
    tests = [t["label"] for t in tests]
    return {
        "name": "{} {} Tests".format(fpga["human_name"], human_name),
        "board": fpga["ci_board"],
        "id": job_id,
        "tests": tests,
    }


def schedule_by_tag(db: TestDatabase, human_name: str, fpga: str, job_id: str, tags: list[str],
                    label_prefix = None):
    """
    Create a schedule for a list of tests in the DB which match all tags in the given list and
    whose label starts with the given prefix (optional).
    """
    def match_fn(test):
        if label_prefix and not test["label"].startswith(label_prefix):
            return False
        return all(tag in test["tags"] for tag in tags)
    return create_schedule(human_name, fpga, job_id, db.schedule_tests(match_fn))


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
        "--test_tag_filters",
        action="append",
        default=[],
        help="List of tags, using the same syntax and semantic as bazel --test_tag_filters." +
        "For example, --test_tag_filters=-manual,fpga"
    )
    parser.add_argument(
        "query",
        default=['//...'],
        metavar="QUERY...",
        nargs='*',
        help="Arguments forwarded to bazel cquery to list targets",
    )
    args = parser.parse_args()

    bad_tags = []
    good_tags = []
    for tags in args.test_tag_filters:
        for tag in tags.split(','):
            if tag.startswith('-'):
                bad_tags.append(tag[1:])
            else:
                good_tags.append(tag)

    query_file = tempfile.NamedTemporaryFile(mode="wt", delete=False)
    query_file.write(TEST_INFO_QUERY)
    query_file.close()

    initial_args = [
        "./bazelisk.sh",
        "cquery",
        "--output=starlark",
        f"--starlark:file={query_file.name}",
    ]

    if args.explain:
        print("Running: {}".format(initial_args + args.query), file=sys.stderr)
    res = subprocess.check_output(
        initial_args + args.query,
        text = True,
    )
    test_db = TestDatabase(args.explain, bad_tags, good_tags)
    for line in res.splitlines():
        test_db.add_test(line)

    args.out_dir.mkdir(exist_ok = True)

    # Schedule all jobs.
    jobs = []

    def sched(human_name, fpga, id, tags, label_prefix = None):
        jobs.append(schedule_by_tag(test_db, human_name, fpga, id, tags, label_prefix))
    sched("Manufacturing", "cw340", "cw340_manuf", ["manuf", "cw340"])
    sched("Manufacturing", "cw310", "cw310_manuf", ["manuf", "cw310"])
    sched("SiVal ROM_EXT", "cw340", "cw340_sival_rom_ext", ["cw340_sival_rom_ext"])
    sched("SiVal ROM_EXT", "cw310", "cw310_sival_rom_ext", ["cw310_sival_rom_ext"])
    sched("SiVal", "cw340", "cw340_sival", ["cw340_sival"])
    sched("SiVal", "cw310", "cw310_sival", ["cw310_sival"])
    # There are too many ROM_EXT tests to fit in one job so we split out the ownership and rescue
    # tests, and schedule the rest together.
    sched("ROM_EXT (ownership)", "cw340", "cw340_ownership", ["cw340_rom_ext"],
          label_prefix = "@@//sw/device/silicon_creator/rom_ext/e2e/ownership:")
    sched("ROM_EXT (rescue)", "cw340", "cw340_rescue", ["cw340_rom_ext"],
          label_prefix = "@@//sw/device/silicon_creator/rom_ext/e2e/rescue:")
    sched("ROM_EXT (remaining)", "cw340", "cw340_rom_ext", ["cw340_rom_ext"])
    sched("ROM_EXT", "cw310", "cw310_rom_ext", ["cw310_rom_ext"])

    sched("ROM", "cw340", "cw340_rom", ["cw340_rom_with_fake_keys"])
    sched("ROM", "cw310", "cw310_rom", ["cw310_rom_with_fake_keys"])
    sched("TestROM", "cw340", "cw340_rom", ["cw340_test_rom"])
    sched("TestROM", "cw310", "cw310_rom", ["cw310_test_rom"])

    for job in jobs:
        tests = job.pop("tests")
        target_file = "{}.txt".format(job["id"])
        job["target_file"] = target_file
        (args.out_dir / target_file).write_text("\n".join(tests))

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
