#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from pathlib import Path
import hjson
import csv


class Testplan:
    testpoints: list[dict]
    OPTIONAL_FIELDS = [
        "bazel",
        "lc_states",
        "features",
        "boot_stages",
        "tags",
        "otp_mutate",
        "host_support",
    ]

    def __init__(self, testplan: dict):
        self.testpoints = testplan["testpoints"]
        for test in self.testpoints:
            test["ip"] = testplan.get("name", "unknown")
            for f in self.OPTIONAL_FIELDS:
                if f not in test:
                    test[f] = "None"

    def join(self, other: "Testplan") -> None:
        self.testpoints.extend(other.testpoints)

    def debug(self) -> None:
        print(hjson.dumps(self.testpoints, indent=4))

    def json(self, outpath: Path) -> None:
        with open(outpath, "w") as f:
            hjson.dump(self.testpoints, f, indent=4)
        print(f"Generated {outpath}.")

    def csv(self, outpath: Path) -> None:
        headers = self.testpoints[0].keys()
        with open(outpath, "w") as f:
            writer = csv.DictWriter(f, fieldnames=headers)
            writer.writeheader()
            writer.writerows(self.testpoints)
        print(f"Generated {outpath}.")

    @staticmethod
    def from_top(top_path: Path) -> "Testplan":
        repo_path = find_repo_dir(top_path)
        top_testplan = hjson.load(top_path.open("r"))
        this = Testplan(top_testplan)
        for file in top_testplan["import_testplans"]:
            testplan = hjson.load(open(repo_path / file, "r"))
            this.join(Testplan(testplan))
        return this


def find_repo_dir(p: Path) -> Path:
    """
    Finds the repository absolute path from a given path.
    """
    current = p.absolute()
    while True:
        marker = current / ".git"
        if marker.is_file():
            return current

        if current == current.parent:
            print("Warning: could not find repository absolut path.")
            return Path("./").absolute()
        current = current.parent
