"""Helper to aggregate all metadata from a test in one place"""

# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from enum import Enum
import pathlib3x as pathlib
from typing import Optional, List
import dataclasses
from typeguard import typechecked

import scripts_lib

import logging
logger = logging.getLogger(__name__)


class Failure_Modes(Enum):
    """Descriptive enum for the mode in which a test fails"""

    NONE = 0
    TIMEOUT = 1  # The simulation process did not complete within the timeout
    FILE_ERROR = 2  # There was a problem attempting to open a logfile
    LOG_ERROR = 3  # The contents of a logfile met a criterion for test failure

    def __str__(self):
        """Print enumerated values as e.g. TIMEOUT(1)"""
        return f'{self.name}({self.value})'

@typechecked
@dataclasses.dataclass
class TestRunResult(scripts_lib.testdata_cls):
    """Holds metadata about a single test and its results.

    Most of the fields aren't actually optional to running
    the simulations, but they may be optional in that we haven't yet
    populated the field or generated the item yet.
    """
    passed: Optional[bool] = None                # True if test passed
    # Message describing failure, includes a '[FAILED]: XXXX' line at the end.
    failure_mode: Optional[Failure_Modes] = None
    failure_message: Optional[str] = None

    testdotseed: Optional[str] = None
    testname: Optional[str] = None        # Name of test
    seed: Optional[int] = None            # Seed of test
    binary: Optional[pathlib.Path] = None # Path to test binary
    rtl_simulator: Optional[str] = None   # Which simulator is used
    iss_cosim: Optional[str] = None       # Which ISS are we cosimulating with?

    # RISCV_DV specific test parameters
    gen_test: Optional[str] = None
    gen_opts: Optional[str] = None
    rtl_test: Optional[str] = None
    sim_opts: Optional[str] = None

    dir_test: Optional[pathlib.Path] = None
    assembly: Optional[pathlib.Path] = None         # Path to assembly file
    objectfile: Optional[pathlib.Path] = None

    riscvdv_run_gen_log: Optional[pathlib.Path] = None
    riscvdv_run_gen_stdout: Optional[pathlib.Path] = None
    riscvdv_run_log: Optional[pathlib.Path] = None
    riscvdv_run_stdout: Optional[pathlib.Path] = None
    compile_asm_gen_log: Optional[pathlib.Path] = None
    compile_asm_log: Optional[pathlib.Path] = None

    rtl_log: Optional[pathlib.Path] = None          # Path to UVM DV simulation log
    rtl_stdout: Optional[pathlib.Path] = None
    rtl_trace: Optional[pathlib.Path] = None        # Path to RTL ibex trace output
    iss_cosim_log: Optional[pathlib.Path] = None
    iss_cosim_trace: Optional[pathlib.Path] = None  # Path to cosim_trace logfile

    dir_fcov: Optional[pathlib.Path] = None

    riscvdv_run_gen_cmds: Optional[List[List[str]]] = None
    riscvdv_run_cmds: Optional[List[List[str]]] = None
    compile_asm_gen_cmds: Optional[List[str]] = None
    compile_asm_cmds: Optional[List[List[str]]] = None
    rtl_cmds: Optional[List[List[str]]] = None

    metadata_pickle_file: pathlib.Path = None
    pickle_file: Optional[pathlib.Path] = None
    yaml_file: Optional[pathlib.Path] = None

    @classmethod
    @typechecked
    def construct_from_metadata_dir(cls, dir_metadata: pathlib.Path, tds: str):
        """Construct metadata object from exported object using default filenames."""

        trr_pickle = dir_metadata / f"{tds}.pickle"
        trr = cls.construct_from_pickle(trr_pickle)
        return trr

    def format_to_printable_dict(self) -> dict:
        """Overwrite the default method in scripts_lib.testdata_cls.

        Format to a printable dict, but for any pathlib.Path strings, print them
        as relative to the test directory. More useful for human scanning.
        """
        relative_dict = {}
        for k, v in dataclasses.asdict(self).items():
            if (isinstance(v, pathlib.Path) and v.is_relative_to(self.dir_test)):
                relative_dict[k] = str(v.relative_to(self.dir_test))
            else:
                relative_dict[k] = v

        return scripts_lib.format_dict_to_printable_dict(relative_dict)
