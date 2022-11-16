#!/usr/bin/env python3
"""Hold build metadata/configuration in a central location."""

# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import sys
import os
from types import *
import pathlib3x as pathlib
import pickle
import typing
from typing import Optional, Union, List, Tuple
from enum import Enum
import argparse
import shlex
import dataclasses
from dataclasses import field
from typeguard import typechecked
import portalocker
import signal

import setup_imports
import scripts_lib
import ibex_cmd
import ibex_config
import lib as riscvdv_lib
from test_run_result import TestRunResult

import logging
logger = logging.getLogger(__name__)


@typechecked
@dataclasses.dataclass
class RegressionMetadata(scripts_lib.testdata_cls):
    """Holds metadata about the current builds.

    Optional fields mean that they haven't yet been populated.
    """

    dir_out: pathlib.Path = pathlib.Path()
    dir_metadata: pathlib.Path = pathlib.Path()
    pickle_file : pathlib.Path = field(init=False, compare=False, default_factory=pathlib.Path)
    yaml_file   : pathlib.Path = field(init=False, compare=False, default_factory=pathlib.Path)

    raw_args_str: str = ' ' # The arguments passed in to the constructor
    raw_args_dict: dict = field(default_factory=dict)
    seed: int = 1  # starting seed
    waves: bool = False
    cov: bool = False
    cosim: bool = True
    simulator: str = ' '
    iss: str = ' '
    test: str = ' '
    verbose: bool = False
    iterations: Optional[int] = None
    signature_addr: str = ' '
    ibex_config: str = ' '
    dut_cov_rtl_path: str = ''

    tests_and_counts: List[Tuple[str, int]] = field(default_factory=list)
    isa_ibex: Optional[str] = None
    isa_iss: Optional[str] = None
    run_rtl_timeout_s: int = 1800

    # Files that control the regression, specify configurations, tests, etc
    ibex_configs                : pathlib.Path = field(init=False, compare=False, default_factory=pathlib.Path)
    ibex_riscvdv_simulator_yaml : pathlib.Path = field(init=False, compare=False, default_factory=pathlib.Path)
    ibex_riscvdv_customtarget   : pathlib.Path = field(init=False, compare=False, default_factory=pathlib.Path)
    ibex_riscvdv_testlist       : pathlib.Path = field(init=False, compare=False, default_factory=pathlib.Path)
    ibex_riscvdv_csr            : pathlib.Path = field(init=False, compare=False, default_factory=pathlib.Path)

    # Build logs and commands
    riscvdv_build_log           : Optional[pathlib.Path]    = None
    riscvdv_build_stdout        : Optional[pathlib.Path]    = None
    riscvdv_build_cmds          : Optional[List[List[str]]] = None
    tb_build_log                : Optional[pathlib.Path]    = None
    tb_build_stdout             : Optional[pathlib.Path]    = None
    tb_build_cmds               : Optional[List[List[str]]] = None
    riscvdv_fcov_log            : Optional[pathlib.Path]    = None
    riscvdv_fcov_stdout         : Optional[pathlib.Path]    = None
    riscvdv_fcov_cmds           : Optional[List[List[str]]] = None
    cov_merge_db_list           : Optional[pathlib.Path]    = None
    cov_merge_log               : Optional[pathlib.Path]    = None
    cov_merge_stdout            : Optional[pathlib.Path]    = None
    cov_merge_cmds              : Optional[List[List[str]]] = None
    cov_report_log              : Optional[pathlib.Path]    = None
    cov_report_stdout           : Optional[pathlib.Path]    = None
    cov_report_cmds             : Optional[List[List[str]]] = None
    regr_log                    : Optional[pathlib.Path]    = None
    regr_log_junit              : Optional[pathlib.Path]    = None
    regr_log_junit_merged       : Optional[pathlib.Path]    = None

    environment_variables       : dict = field(init=False, compare=False, default_factory=dict)

    # Project directories (which contain above files and results)
    ibex_root                   : pathlib.Path = field(init=False, compare=False, default_factory=pathlib.Path)
    riscvdv_root                : pathlib.Path = field(init=False, compare=False, default_factory=pathlib.Path)
    ot_lowrisc_ip               : pathlib.Path = field(init=False, compare=False, default_factory=pathlib.Path)
    ot_xcelium_cov_scripts      : pathlib.Path = field(init=False, compare=False, default_factory=pathlib.Path)
    ibex_dv_root                : pathlib.Path = field(init=False, compare=False, default_factory=pathlib.Path)
    dir_build                   : pathlib.Path = field(init=False, compare=False, default_factory=pathlib.Path)
    dir_instruction_generator   : pathlib.Path = field(init=False, compare=False, default_factory=pathlib.Path)
    dir_tb                      : pathlib.Path = field(init=False, compare=False, default_factory=pathlib.Path)
    dir_run                     : pathlib.Path = field(init=False, compare=False, default_factory=pathlib.Path)
    dir_cov                     : pathlib.Path = field(init=False, compare=False, default_factory=pathlib.Path)
    dir_fcov                    : pathlib.Path = field(init=False, compare=False, default_factory=pathlib.Path)
    dir_shared_cov              : pathlib.Path = field(init=False, compare=False, default_factory=pathlib.Path)
    dir_cov_merged              : pathlib.Path = field(init=False, compare=False, default_factory=pathlib.Path)
    dir_cov_report              : pathlib.Path = field(init=False, compare=False, default_factory=pathlib.Path)

    tests_pickle_files: Optional[List[pathlib.Path]] = None

    def __post_init__(self):
        """Construct all the dependent metadata."""
        self._setup_directories()
        self.pickle_file                 = self.dir_metadata/'metadata.pickle'
        self.yaml_file                   = self.dir_metadata/'metadata.yaml'
        self.ibex_configs                = self.ibex_root/'ibex_configs.yaml'
        self.ot_xcelium_cov_scripts      = self.ot_lowrisc_ip/'dv'/'tools'/'xcelium'
        self.ibex_riscvdv_simulator_yaml = self.ibex_dv_root/'yaml'/'rtl_simulation.yaml'
        self.ibex_riscvdv_customtarget   = self.ibex_dv_root/'riscv_dv_extension'
        self.ibex_riscvdv_testlist       = self.ibex_riscvdv_customtarget/'testlist.yaml'
        self.ibex_riscvdv_csr            = self.ibex_riscvdv_customtarget/'csr_description.yaml'

        self.environment_variables       = dict(os.environ)

    def _get_ibex_metadata(self):
        """Get the desired ibex_config parameters.

        # Any extra derivative data can be setup here.
        """
        if self.iterations is not None and self.iterations <= 0:
            raise RuntimeError('Bad --iterations argument: must be positive')
        if self.seed < 0:
            raise RuntimeError('Bad --start_seed argument: must be non-negative')

        cfg = ibex_cmd.get_config(self.ibex_config)
        self.isa_ibex, self.isa_iss = ibex_cmd.get_isas_for_config(cfg)
        self.tests_and_counts = self.get_tests_and_counts()


    def _setup_directories(self):
        """Set the directory variables which contain all other build factors."""
        self.ibex_root                   = setup_imports._IBEX_ROOT
        self.riscvdv_root                = setup_imports._RISCV_DV
        self.ot_lowrisc_ip               = setup_imports._OT_LOWRISC_IP
        self.ibex_dv_root                = setup_imports._CORE_IBEX
        self.dir_build                   = self.dir_out/'build'
        self.dir_instruction_generator   = self.dir_build/'instr_gen'
        self.dir_tb                      = self.dir_build/'tb'
        self.dir_run                     = self.dir_out/'run'
        self.dir_tests                   = self.dir_run/'tests'
        self.dir_cov                     = self.dir_run/'coverage'
        self.dir_fcov                    = self.dir_cov/'fcov'
        self.dir_shared_cov              = self.dir_cov/'shared_cov'
        self.dir_cov_merged              = self.dir_cov/'merged'
        self.dir_cov_report              = self.dir_cov/'report'

    @classmethod
    def arg_list_initializer(cls,
                            dir_metadata: pathlib.Path,
                            dir_out: pathlib.Path,
                            args_list: str):
        """Initialize fields from an input str of 'KEY=VALUE KEY2=VALUE2' form.

        Usings args_list: str is convenient for constructing from a higher level,
        such as a makefile.

        dir_metadata/dir_out are always required.
        dir_metadata -> Where build metadata is stored and reconstructed from.
        dir_out -> Where the build takes place.
        dir_metadata can be outside of dir_out, but placing it inside of dir_out
        makes cleanup for a new build easy. ('rm -rf dir_out/')

        Returns a constructed RegressionMetadata object.
        """
        if dir_out is pathlib.Path():
            raise RuntimeError("self.dir_metadata must be initialized)")
        if dir_metadata is pathlib.Path():
            raise RuntimeError("self.dir_metadata must be initialized)")

        dummy_obj = RegressionMetadata()
        dummy = dataclasses.asdict(dummy_obj)
        logger.debug(dummy)  # Useful to see types of all the k,v pairs

        # Any fields declared in the class initialization (see above) can be populated
        # by constructing a dict with keys matching the fields, and then passing **dict
        # to the construction of the class. We do this here to populate from 'args_list'.
        args_dict = {}
        args_dict['raw_args_str'] = args_list
        args_dict['raw_args_dict'] = {k: v for k, v in
                                      (pair.split('=', maxsplit=1)
                                       for pair in shlex.split(args_list))}

        kv_tuples = (pair.split('=', maxsplit=1) for pair in shlex.split(args_list))
        kv_dict = {k.lower(): v for k, v in kv_tuples}

        for f in dataclasses.fields(dummy_obj):
            if f.name in kv_dict:

                key = f.name
                val = kv_dict[f.name]

                logger.debug(f"Attempting to set {key} in metadata object")
                logger.debug(f"Type of key '{key}' is {f.type}, value is {type(val)}")

                # There should be a better way to do typecasting...
                # i.e. how to check that the value of any k:v pair passed to
                # --args-list can be typecast from str to the typehint of
                # the matching class variable defined above.
                # Eg. args_dict[key] = cast(f.type, val)
                # logger.error(f"{pair},{key},{val},{type(val),{type(dummy[key])}}")
                if f.type is str:
                    args_dict[key] = str(val)
                elif f.type is int:
                    args_dict[key] = int(val)
                elif f.type is bool:
                    args_dict[key] = bool(int(val))
                elif f.type is pathlib.Path:
                    args_dict[key] = pathlib.Path(val)
                elif f.type is typing.Optional[int]:
                    if val:
                        args_dict[key] = int(val)
                    else:
                        args_dict[key] = None
                elif f.type is NoneType:
                    args_dict[key] = None
                else:
                    raise RuntimeError(f"Couldn't set key '{key}' in metadata object! "
                                       f"Expected type : {type(dummy[key])}")

        # Finally construct the metadata object
        md = cls(
            dir_out=dir_out.resolve(),
            dir_metadata=dir_metadata.resolve(),
            **args_dict)

        # Fetch/set more derivative metadata specific to the ibex
        md._get_ibex_metadata()

        return md

    @classmethod
    @typechecked
    def construct_from_metadata_dir(cls, dir_metadata: pathlib.Path):
        """Construct metadata object from exported object using default filenames."""
        md_pickle = pathlib.Path(dir_metadata)/'metadata.pickle'
        md = cls.construct_from_pickle(md_pickle)
        return md

    def get_tests_and_counts(self) -> List[Tuple[str, int]]:
        """Get a list of tests and the number of iterations to run of each.

        ibex_config should be the name of the Ibex configuration to be tested.

        If test is provided, it gives the test or tests (as a comma separated
        string) to narrow to. Use the special name "all" to run all the tests.

        If iterations is provided, it should be a positive number and overrides the
        number of iterations for each test.

        """
        rv_testlist = self.ibex_riscvdv_testlist
        rv_test = self.test if self.test is not None else 'all'
        rv_iterations = self.iterations or 0

        # Get all the tests that match the test argument, scaling as necessary with
        # the iterations argument.
        matched_list = []  # type: _TestEntries
        riscvdv_lib.process_regression_list(
            testlist=rv_testlist,
            test=rv_test,
            iterations=rv_iterations,
            matched_list=matched_list,
            riscv_dv_root=self.riscvdv_root)
        if not matched_list:
            raise RuntimeError("Cannot find {} in {}".format(self.test, self.testlist))

        # Filter tests by the chosen ibex configuration
        filtered_list = ibex_cmd.filter_tests_by_config(
            ibex_config.parse_config(self.ibex_config, str(self.ibex_configs)),
            matched_list)

        # Convert to desired output format (and check for well-formedness)
        ret = []
        for test in filtered_list:
            name = test['test']
            iterations = test['iterations']
            assert isinstance(name, str) and isinstance(iterations, int)
            assert iterations > 0
            ret.append((name, iterations))

        return ret

    def tds(self, give_tuple: bool = False) -> Union[List[str],
                                                     List[Tuple[str, int]]]:
        """Return the TEST.SEED strings for all the tests configured in the regression.

        By default returns a list of strs which are TEST.SEED, but can return a list of
        tuples as (TEST, SEED)
        """
        if not self.tests_and_counts:
            raise RuntimeError("self.tests_and_counts is empty, cant get TEST.SEED strings.")
        tds_list = []
        for test, count in self.tests_and_counts:
            for i in range(count):
                if give_tuple:
                    tds = (test, self.seed + i)
                else:
                    tds = f"{test}.{self.seed + i}"
                tds_list.append(tds)

        return tds_list




class Ops(Enum):
    """Type of operations that can be specified by an argparse arg."""

    CREATE = 'create_metadata'
    PRINT_FIELD = 'print_field'
    TESTS_AND_SEEDS = 'tests_and_seeds'

    def __str__(self):
        return self.value


def _main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--op', type=Ops, choices=Ops, required=True)
    parser.add_argument('--dir-metadata', type=pathlib.Path, required=True)
    parser.add_argument('--dir-out', type=pathlib.Path, required=False)
    parser.add_argument('--args-list', type=str, required=False)
    parser.add_argument('--field', type=str, required=False)

    args = parser.parse_args()

    # Parse all variables from the argument string, and then add them
    # to the metadata object

    if args.op == Ops.CREATE:
        """
        Use the --args-list input, a string of 'KEY=VALUE KEY2=VALUE2',
        to create a new metadata object.
        --dir-metadata specifies the directory of the test metadata
        --dir-out specifies the directory for the regression build and test to take place
        """
        if (pathlib.Path(args.dir_metadata)/'metadata.pickle').exists():
            logger.error("Build metadata already exists, not recreating from scratch.")
            return

        md = RegressionMetadata.arg_list_initializer(dir_metadata=pathlib.Path(args.dir_metadata),
                                                     dir_out=pathlib.Path(args.dir_out),
                                                     args_list=args.args_list)

        # Setup metadata objects for each of the tests to be run. Construct a list of these
        # objects inside the regression_metadata object constructed above, so we can easily
        # find and import them later, and give each test object a link back to this top-level
        # object that defines the wider regression.

        md.tests_pickle_files = []
        for test, seed in md.tds(give_tuple=True):
            tds_str = f"{test}.{seed}"
            trr_pickle_file = md.dir_metadata / (tds_str + ".pickle")

            # Initialize TestRunResult object
            trr = TestRunResult(
                passed=None,
                failure_message=None,
                testdotseed=tds_str,
                testname=test,
                seed=seed,
                rtl_simulator=md.simulator,
                iss_cosim=md.iss,
                dir_test=md.dir_tests / tds_str,
                metadata_pickle_file=md.pickle_file,
                pickle_file=trr_pickle_file,
                yaml_file=(md.dir_tests / tds_str / 'trr.yaml'))

            # Save the path into a list in the regression metadata object for later.
            md.tests_pickle_files.append(trr.pickle_file)
            # Export the trr structure to disk.
            trr.export(write_yaml=True)

        # Export here to commit new RegressionMetadata object to disk.
        md.export(write_yaml=True)

    if args.op == Ops.PRINT_FIELD:

        md = RegressionMetadata.construct_from_metadata_dir(args.dir_metadata)

        value = getattr(md, args.field)
        if value is None:
            raise RuntimeError("Field requested is not present or not set in the regression metadata object")

        logger.debug(f"Returning value of field {args.field} as {value}")
        print(str(value))  # Captured into Makefile variable

    if args.op == Ops.TESTS_AND_SEEDS:
        """Return a list of TEST.SEED for all the valid tests"""

        md = RegressionMetadata.construct_from_metadata_dir(args.dir_metadata)
        for tds in md.tds():
            print(tds)


class LockedMetadata():
    """Construct instance of RegressionMetadata, while locking the on-disk file.

    This allows us to not worry about multiple processes racing to write
    into the file. This could have performance implications if there
    is strict dependencies between steps, so aim to only hold this lock
    for as short time as possible.

    N.B. When used as follows....
    '''
    with LockedMetadata(args.dir_metadata, __file__) as md:
        print(md.simulator)
        # etc...

    print(md.ibex_config) # !!!!!!
    '''
    ... after the with-context is over, the file is closed and we have committed any
    changes made to disk, but the object 'md' in memory is still around and useable.
    Therefore, it is still valid to reference it after the scope has ended.
    """

    def _handler(signum, frame, other):
        logger.error(f"Timed-out [5s] waiting to open the regression metadata file! (signal = {signum})")
        raise OSError("Couldn't open regression metadata file before we were timed out!")

    def __init__(self, dir_metadata: pathlib.Path, script: pathlib.Path):
        """Construct object corresponding to the on-disk file.

        Args:
            dir_metadata: Directory containing the regression metadata
            script: Name of the file locking the metadata. Only used for logging.
        """
        self.pickle_file = pathlib.Path(dir_metadata)/'metadata.pickle'
        self.file_name = pathlib.Path(script).name

    def __enter__(self):
        """Provide a way to access the in-filesystem object safely (holds a lock)."""
        # Set the signal handler and a 5-second alarm
        # Since other scripts may lock this file, better implement a timeout
        # to report what went wrong. Though we should never be racing/locking
        # for all that long, this is just a backup.
        signal.signal(signal.SIGALRM, self._handler)
        signal.alarm(5)  # 5s

        self.handle = self.pickle_file.open('rb')
        portalocker.lock(self.handle, portalocker.LockFlags.EXCLUSIVE)
        logger.info(f"Locking metadata file for {self.file_name}...")
        self.md = pickle.load(self.handle)

        signal.alarm(0)  # Disable the alarm

        return self.md

    def __exit__(self, type, value, traceback):
        """Close our exclusive access to the file, committing any changes to disk."""
        self.md.export(write_yaml=True)
        logger.info(f"Unlocked in {self.file_name}.")
        portalocker.unlock(self.handle)
        self.handle.close()


if __name__ == '__main__':
    sys.exit(_main())
