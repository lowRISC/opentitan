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
    path = re.sub(r'^bazel-out/k8[^/]*/bin/', 'generated/', path)
    return path


class CoverageCollection:
    """Builder for the aggregated coverage data used by the interactive viewer."""

    def __init__(self, source_dir: Optional[Path] = None) -> None:
        """Initializes the collection with an optional source root directory."""
        self.tests: List[str] = []
        self.views: List[str] = []
        self.files: Dict[str, Any] = {}
        self.loaded_sources: Dict[str, str] = {}
        self.source_dir = source_dir

    def add_test(self,
                 test_label: str,
                 file_profiles: Dict[str, FileProfile],
                 is_view: bool = False) -> None:
        """Adds coverage data from a specific test or view to the collection."""
        if is_view:
            test_idx = len(self.views)
            self.views.append(test_label)
            key = 'v'
        else:
            test_idx = len(self.tests)
            self.tests.append(test_label)
            key = 't'

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
                        "t": [],
                        "v": []
                    } for line in contents],
                    "f": [],
                }

            lines = self.files[path]["l"]

            # Update line coverage data
            for lineno, count in profile.da.items():
                lineid = lineno - 1
                if 0 <= lineid < len(lines):
                    lines[lineid]['s'] = False
                    # Views include all lines defined in the LCOV (even with 0 hits)
                    # Tests only include lines with actual hits (count > 0)
                    if is_view or count > 0:
                        if test_idx not in lines[lineid][key]:
                            lines[lineid][key].append(test_idx)

            # Update function coverage data
            funcs = self.files[path]["f"]
            for func_name, fn_lines in profile.fn.items():
                for lineno in fn_lines:
                    lineid = lineno - 1
                    for f in funcs:
                        if f["n"] == func_name and f["l"] == lineid:
                            func_entry = f
                            break
                    else:
                        func_entry = {
                            "n": func_name,
                            "l": lineid,
                            "t": [],
                            "v": []
                        }
                        funcs.append(func_entry)

                    fnda_count = profile.fnda.get(func_name, 0)
                    if is_view or fnda_count > 0:
                        if test_idx not in func_entry[key]:
                            func_entry[key].append(test_idx)

    def _fix_test_fn_hit(self) -> None:
        """Marks a function as covered if its definition line is covered."""
        for path, data in self.files.items():
            lines = data["l"]
            for func_entry in data["f"]:
                lineid = func_entry["l"]
                if 0 <= lineid < len(lines):
                    # Sync test hits.
                    # NOTE: DO NOT sync view hits to keep the list accurate.
                    for test_idx in lines[lineid]["t"]:
                        if test_idx not in func_entry["t"]:
                            func_entry["t"].append(test_idx)

    def as_dict(self) -> Dict[str, Any]:
        """Returns the aggregated coverage data as a dictionary."""
        self._fix_test_fn_hit()
        return {"tests": self.tests, "views": self.views, "files": self.files}
