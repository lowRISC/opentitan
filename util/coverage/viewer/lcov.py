# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Parser for LCOV coverage data files."""

import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, List, Iterator, NamedTuple, Optional


@dataclass
class FileProfile:
    """Coverage profile for a single source file."""
    sf: str
    fn: Dict[str, int] = field(default_factory=dict)  # name -> lineno
    fnda: Dict[str, int] = field(default_factory=dict)  # name -> count
    da: Dict[int, int] = field(default_factory=dict)  # lineno -> count


class LcovTestProfile(NamedTuple):
    """Aggregate coverage data for a specific test execution."""
    name: str
    files: Dict[str, FileProfile]


def parse_lcov(lines: List[str]) -> Dict[str, FileProfile]:
    """Parses LCOV lines into a mapping of file paths to their profiles."""
    files: Dict[str, FileProfile] = {}
    current_profile = None

    for line in lines:
        line = line.strip()
        if not line:
            continue

        if ':' in line:
            tag, params = line.split(':', 1)
        else:
            tag, params = line, ''

        if tag == 'SF':
            sf_path = params
            if sf_path not in files:
                files[sf_path] = FileProfile(sf=sf_path)
            current_profile = files[sf_path]
        elif tag == 'FN':
            if current_profile and ',' in params:
                try:
                    f_lineno_str, f_name = params.split(',')
                    current_profile.fn[f_name] = int(f_lineno_str)
                except ValueError:
                    continue
        elif tag == 'FNDA':
            if current_profile and ',' in params:
                try:
                    f_count_str, f_name = params.split(',')
                    current_profile.fnda[f_name] = (
                        current_profile.fnda.get(f_name, 0) + int(f_count_str))
                except ValueError:
                    continue
        elif tag == 'DA':
            if current_profile and ',' in params:
                try:
                    parts = params.split(',')
                    da_lineno = int(parts[0])
                    da_count = int(parts[1])
                    current_profile.da[da_lineno] = (
                        current_profile.da.get(da_lineno, 0) + da_count)
                except ValueError:
                    continue
        elif tag == 'end_of_record':
            current_profile = None

    return files


def iter_lcov_files(lcov_files_list_path: Path,
                    coverage_dir: Optional[Path] = None) -> \
        Iterator[LcovTestProfile]:
    """Iterates over LCOV files listed in a file, yielding their profiles."""
    with open(lcov_files_list_path, 'r') as f:
        for line in f:
            lcov_path = Path(line.strip())
            if coverage_dir and not lcov_path.is_absolute():
                lcov_path = coverage_dir / lcov_path

            if lcov_path.name != 'coverage.dat':
                continue
            if lcov_path.exists():
                # Calculate test label: //path/after/testlogs:test_name
                parts = lcov_path.parent.parts
                try:
                    testlogs_index = parts.index('testlogs')
                    test_dir = '/'.join(parts[testlogs_index + 1:-1])
                    test_name = f'//{test_dir}:{parts[-1]}'
                except ValueError:
                    # Fallback to filename if 'testlogs' not in path
                    test_name = lcov_path.parent.name

                with open(lcov_path, 'r') as lcov_f:
                    yield LcovTestProfile(name=test_name,
                                          files=parse_lcov(lcov_f.readlines()))
            else:
                print(f"Warning: LCOV file not found: {lcov_path}",
                      file=sys.stderr)
