#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from pathlib import Path
import hjson
import csv
import re
from dataclasses import dataclass


@dataclass
class Testplan:
    testpoints: list[dict]

    def get_bazel(self) -> list[str]:
        """
        Return a unique list of bazel targets
        """
        res = [item for tp in self.testpoints for item in tp.get("bazel", [])]
        return list(sorted(set(res)))

    def get_si_stage(self) -> list[str]:
        """
        Return a unique list of Sival stage
        """
        res = [tp["si_stage"] for tp in self.testpoints]
        res = filter(lambda item: item.lower() not in ["na", "none"], res)
        return list(sorted(set(res)))

    def get_lc_states(self) -> list[str]:
        """
        Return a unique list of life-cycle stages
        """
        res = [state for tp in self.testpoints for state in tp.get("lc_states", [])]
        return list(sorted(set(res)))

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

    def filter_testpoints(
        self, name: str = ".*", stage: str = ".*", si_stage: str = ".*", lc_state: str = ".*"
    ) -> "Testplan":
        """
        Apply filters to remove testpoints or rows if exported to csv.
        """

        def check(node: dict) -> bool:
            return (
                bool(re.match(name, node["name"]))
                and bool(re.match(stage, node["stage"]))
                and bool(re.match(si_stage, node["si_stage"]))
                and any([re.match(lc_state, state) for state in node["lc_states"]])
            )

        filtered = filter(check, self.testpoints)
        return Testplan(list(filtered))

    def filter_fields(self, fields: list[str] | None = None) -> "Testplan":
        """
        Apply filters to remove fields of testpoints or columns if exported to csv.
        """
        if fields is None:
            return self

        testpoints = []
        for tp in self.testpoints:
            filtered = filter(lambda item: item[0] in fields, tp.items())
            testpoints.append(dict(filtered))
        return Testplan(testpoints)

    @staticmethod
    def from_dict(testplan: dict) -> "Testplan":
        OPTIONAL_FIELDS = {
            "bazel": lambda: [],
            "lc_states": lambda: [],
            "features": lambda: [],
            "boot_stages": lambda: [],
            "tags": lambda: [],
            "otp_mutate": lambda: False,
            "host_support": lambda: False,
            "si_stage": lambda: "None",
        }
        testpoints = testplan["testpoints"]
        for test in testpoints:
            test["ip"] = testplan.get("name", "unknown")
            for f, default in OPTIONAL_FIELDS.items():
                if f not in test:
                    test[f] = default()

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
