# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Manages aggregated coverage data for the interactive viewer."""

import re
from pathlib import Path
from typing import Dict, List, Any, Optional

from util.coverage.viewer.lcov import FileProfile


def simplify_path(path: str) -> str:
    """Simplifies bazel-out paths to a more consistent 'generated/' prefix."""
    # Simplify bazel-out paths
    path = re.sub(r'^bazel-out/k8[^/]*/', 'generated/', path)
    return path


class CoverageCollection:
    """Builder for the aggregated coverage data used by the interactive viewer."""

    def __init__(self, source_dir: Optional[Path] = None) -> None:
        """Initializes the collection with an optional source root directory."""
        self.tests: List[str] = []
        self.files: Dict[str, Any] = {}
        self.loaded_sources: Dict[str, str] = {}
        self.source_dir = source_dir

    def add_test(self,
                 test_label: str,
                 file_profiles: Dict[str, FileProfile],
                 add_uncovered: bool = False) -> None:
        """Adds coverage data from a specific test to the collection."""
        test_idx = len(self.tests)
        self.tests.append(test_label)

        for sf_path, profile in file_profiles.items():
            path = simplify_path(sf_path)

            # Read the source file content if not already loaded
            if sf_path not in self.loaded_sources:
                try:
                    full_sf_path = Path(sf_path)
                    if self.source_dir and not full_sf_path.is_absolute():
                        full_sf_path = self.source_dir / full_sf_path

                    with open(full_sf_path, 'r') as f:
                        self.loaded_sources[sf_path] = f.read()
                except FileNotFoundError:
                    # If source file is missing, we can't show it in the viewer
                    continue

            if path not in self.files:
                contents = self.loaded_sources[sf_path].splitlines()
                self.files[path] = {
                    "l": [{
                        "c": line,
                        "s": True,
                        "t": []
                    } for line in contents],
                    "f": {},
                }

            lines = self.files[path]["l"]

            # Update line coverage data
            for lineno, count in profile.da.items():
                idx = lineno - 1
                if 0 <= idx < len(lines):
                    lines[idx]['s'] = False
                    if add_uncovered or count > 0:
                        if test_idx not in lines[idx]['t']:
                            lines[idx]['t'].append(test_idx)

            # Update function coverage data
            funcs = self.files[path]["f"]
            for func_name, lineno in profile.fn.items():
                idx = lineno - 1
                if func_name not in funcs:
                    funcs[func_name] = {"l": idx, "t": []}

                fnda_count = profile.fnda.get(func_name, 0)
                da_count = profile.da.get(lineno, 0)
                if add_uncovered or fnda_count > 0 or da_count > 0:
                    if test_idx not in funcs[func_name]["t"]:
                        funcs[func_name]["t"].append(test_idx)

    def as_dict(self) -> Dict[str, Any]:
        """Returns the aggregated coverage data as a dictionary."""
        return {"tests": self.tests, "files": self.files}
