#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from pathlib import Path
import hjson
import csv
from dataclasses import dataclass


@dataclass
class Testplan:
    testpoints: list[dict]

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

    def from_dict(testplan: dict) -> "Testplan":
        OPTIONAL_FIELDS = [
            "bazel",
            "lc_states",
            "features",
            "boot_stages",
            "tags",
            "otp_mutate",
            "host_support",
            "si_stage",
        ]
        testpoints = testplan["testpoints"]
        for test in testpoints:
            test["ip"] = testplan.get("name", "unknown")
            for f in OPTIONAL_FIELDS:
                if f not in test:
                    test[f] = "None"

        return Testplan(testpoints)

    @staticmethod
    def from_top(top_path: Path) -> "Testplan":
        repo_path = find_repo_dir(top_path)
        top_testplan = hjson.load(top_path.open("r"))
        this = Testplan.from_dict(top_testplan)
        for file in top_testplan["import_testplans"]:
            testplan = hjson.load(open(repo_path / file, "r"))
            this.join(Testplan.from_dict(testplan))
        return this


def find_repo_dir(p: Path, marker: str = "MODULE.bazel") -> Path:
    """
    Finds the repository absolute path from a given path.
    """
    current = p.absolute()
    while True:
        if (current / marker).exists() or (current / ".git").exists():
            return current

        if current == current.parent:
            print("Warning: could not find repository absolut path.")
            return Path("./").absolute()
        current = current.parent
