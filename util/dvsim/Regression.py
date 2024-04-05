# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from modes import Mode, find_mode, find_mode_list
from Test import Test

import logging as log
import sys
from utils import VERBOSE


class Regression(Mode):
    """
    Abstraction for test sets / regression sets.
    """

    # Maintain a list of tests str
    item_names = []

    def __init__(self, regdict):
        self.name = ""
        self.type = ""

        # The `tests` member is typically a list, but it defaults to None.
        # There are 3 possible cases after all the HJson files are parsed, when
        # this particular regression is supplied to be run:
        #
        # 1. `tests` == None:   This is treated as "run ALL available tests".
        # 2. `tests` == []:     No available tests to run
        # 3. `len(tests)` > 0:  The provided set of tests are run.
        self.tests = None
        self.test_names = []

        self.reseed = None
        self.excl_tests = []  # TODO: add support for this
        self.en_sim_modes = []
        self.en_run_modes = []
        self.pre_build_cmds = []
        self.post_build_cmds = []
        self.pre_run_cmds = []
        self.post_run_cmds = []
        self.build_opts = []
        self.run_opts = []
        super().__init__("regression", regdict)

    @staticmethod
    def create_regressions(regdicts, sim_cfg, tests):
        '''
        Create Test sets from a given list of raw dicts.
        Return a list of test set objects.
        '''

        regression_objs = []
        # Pass 1: Create unique set of test sets by merging test sets with the same name
        for regdict in regdicts:
            # Create a new item
            new_regression_merged = False
            new_regression = Regression(regdict)

            # Check for name conflicts with tests before merging
            if new_regression.name in Test.item_names:
                log.error(
                    "Test names and regression names are required to be unique. "
                    "The regression \"%s\" bears the same name with an existing test. ",
                    new_regression.name)
                sys.exit(1)

            for regression in regression_objs:
                # Merge new one with existing if available
                if regression.name == new_regression.name:
                    regression.merge_mode(new_regression)
                    new_regression_merged = True
                    break

            # Add the new test to the list if not already appended
            if not new_regression_merged:
                regression_objs.append(new_regression)
                Regression.item_names.append(new_regression.name)

        # Pass 2: Process dependencies
        build_modes = getattr(sim_cfg, "build_modes", [])
        run_modes = getattr(sim_cfg, "run_modes", [])

        for regression_obj in regression_objs:
            # Unpack the sim modes
            for sim_mode_obj in find_mode_list(regression_obj.en_sim_modes,
                                               build_modes):
                if sim_mode_obj.is_sim_mode == 0:
                    log.error(
                        "Enabled mode \"%s\" within the regression \"%s\" is not a sim mode",
                        sim_mode_obj.name, regression_obj.name)
                    sys.exit(1)

                # Check if sim_mode_obj's sub-modes are a part of regressions's
                # sim modes- if yes, then it will cause duplication of cmds &
                # opts. Throw an error and exit.
                for sim_mode_obj_sub in sim_mode_obj.en_build_modes:
                    if sim_mode_obj_sub in regression_obj.en_sim_modes:
                        log.error(
                            "Regression \"%s\" enables sim_modes \"%s\" and \"%s\". "
                            "The former is already a sub_mode of the latter.",
                            regression_obj.name, sim_mode_obj_sub,
                            sim_mode_obj.name)
                        sys.exit(1)

                # Check if sim_mode_obj is also passed on the command line, in
                # which case, skip
                if sim_mode_obj.name in sim_cfg.en_build_modes:
                    continue

                # Merge the build and run cmds & opts from the sim modes
                regression_obj.pre_build_cmds.extend(
                    sim_mode_obj.pre_build_cmds)
                regression_obj.post_build_cmds.extend(
                    sim_mode_obj.post_build_cmds)
                regression_obj.build_opts.extend(sim_mode_obj.build_opts)
                regression_obj.pre_run_cmds.extend(sim_mode_obj.pre_run_cmds)
                regression_obj.post_run_cmds.extend(sim_mode_obj.post_run_cmds)
                regression_obj.run_opts.extend(sim_mode_obj.run_opts)

            # Unpack the run_modes
            # TODO: If there are other params other than run_opts throw an
            # error and exit

            # Only merge the pre_run_cmds, post_run_cmds & run_opts from the
            # run_modes enabled
            for run_mode_obj in find_mode_list(regression_obj.en_run_modes,
                                               run_modes):
                # Check if run_mode_obj is also passed on the command line, in
                # which case, skip
                if run_mode_obj.name in sim_cfg.en_run_modes:
                    continue
                regression_obj.pre_run_cmds.extend(run_mode_obj.pre_run_cmds)
                regression_obj.post_run_cmds.extend(run_mode_obj.post_run_cmds)
                regression_obj.run_opts.extend(run_mode_obj.run_opts)

            # Unpack tests
            # If `tests` member resolves to None, then we add ALL available
            # tests for running the regression.
            if regression_obj.tests is None:
                log.log(VERBOSE,
                        "Unpacking all tests in scope for regression \"%s\"",
                        regression_obj.name)
                regression_obj.tests = sim_cfg.tests
                regression_obj.test_names = Test.item_names

            else:
                tests_objs = set()
                regression_obj.test_names = regression_obj.tests
                for test in regression_obj.tests:
                    test_obj = find_mode(test, sim_cfg.tests)
                    if test_obj is None:
                        log.error(
                            "Test \"%s\" added to regression \"%s\" not found!",
                            test, regression_obj.name)
                        continue
                    tests_objs.add(test_obj)
                regression_obj.tests = list(tests_objs)

        # Return the list of tests
        return regression_objs

    def merge_regression_opts(self):
        processed_build_modes = []
        for test in self.tests:
            if test.build_mode.name not in processed_build_modes:
                test.build_mode.pre_build_cmds.extend(self.pre_build_cmds)
                test.build_mode.post_build_cmds.extend(self.post_build_cmds)
                test.build_mode.build_opts.extend(self.build_opts)
                processed_build_modes.append(test.build_mode.name)
            test.pre_run_cmds.extend(self.pre_run_cmds)
            test.post_run_cmds.extend(self.post_run_cmds)
            test.run_opts.extend(self.run_opts)

            # Override reseed if available.
            if self.reseed is not None:
                test.reseed = self.reseed
