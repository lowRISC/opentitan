# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import logging as log
import pprint
import sys

from utils import VERBOSE


class Modes():
    """
    Abstraction for specifying collection of options called as 'modes'. This is
    the base class which is extended for run_modes, build_modes, tests and regressions.
    """

    def self_str(self):
        '''
        This is used to construct the string representation of the entire class object.
        '''
        tname = ""
        if self.type != "":
            tname = self.type + "_"
        if self.mname != "":
            tname += self.mname
        if log.getLogger().isEnabledFor(VERBOSE):
            return "\n<---" + tname + ":\n" + pprint.pformat(self.__dict__) + \
                   "\n--->\n"
        else:
            return tname + ":" + self.name

    def __str__(self):
        return self.self_str()

    def __repr__(self):
        return self.self_str()

    def __init__(self, mdict):
        keys = mdict.keys()
        attrs = self.__dict__.keys()

        if 'name' not in keys:
            log.error("Key \"name\" missing in mode %s", mdict)
            sys.exit(1)

        if not hasattr(self, "type"):
            log.fatal("Key \"type\" is missing or invalid")
            sys.exit(1)

        if not hasattr(self, "mname"):
            self.mname = ""

        for key in keys:
            if key not in attrs:
                log.error(f"Key {key} in {mdict} is invalid. Supported "
                          f"attributes in {self.mname} are {attrs}")
                sys.exit(1)
            setattr(self, key, mdict[key])

    def get_sub_modes(self):
        sub_modes = []
        if hasattr(self, "en_" + self.type + "_modes"):
            sub_modes = getattr(self, "en_" + self.type + "_modes")
        return sub_modes

    def set_sub_modes(self, sub_modes):
        setattr(self, "en_" + self.type + "_modes", sub_modes)

    def merge_mode(self, mode):
        '''
        Merge a new mode with self.
        Merge sub mode specified with 'en_*_modes with self.
        '''

        sub_modes = self.get_sub_modes()
        is_sub_mode = mode.name in sub_modes

        if not mode.name == self.name and not is_sub_mode:
            return False

        # Merge attributes in self with attributes in mode arg, since they are
        # the same mode but set in separate files, or a sub-mode.
        for attr, self_attr_val in self.__dict__.items():
            mode_attr_val = getattr(mode, attr, None)

            # If sub-mode, skip the name fields - they could differ.
            if is_sub_mode and attr in ['name', 'mname']:
                continue

            # If mode's value is None, then nothing to do here.
            if mode_attr_val is None:
                continue

            # If self value is None, then replace with mode's value.
            if self_attr_val is None:
                setattr(self, attr, mode_attr_val)
                continue

            # If they are equal, then nothing to do here.
            if self_attr_val == mode_attr_val:
                continue

            # Extend if they are both lists.
            if isinstance(self_attr_val, list):
                assert isinstance(mode_attr_val, list)
                self_attr_val.extend(mode_attr_val)
                continue

            # If the current val is default, replace with new.
            scalar_types = {str: "", int: -1}
            default_val = scalar_types.get(type(self_attr_val))

            if type(self_attr_val) in scalar_types.keys(
            ) and self_attr_val == default_val:
                setattr(self, attr, mode_attr_val)
                continue

            # Check if their types are compatible.
            if type(self_attr_val) != type(mode_attr_val):
                log.error(
                    "Mode %s cannot be merged into %s due to a conflict "
                    "(type mismatch): %s: {%s(%s), %s(%s)}", mode.name,
                    self.name, attr, str(self_attr_val),
                    str(type(self_attr_val)), str(mode_attr_val),
                    str(type(mode_attr_val)))
                sys.exit(1)

            # Check if they are different non-default values.
            if self_attr_val != default_val and mode_attr_val != default_val:
                log.error(
                    "Mode %s cannot be merged into %s due to a conflict "
                    "(unable to pick one from different values): "
                    "%s: {%s, %s}", mode.name, self.name, attr,
                    str(self_attr_val), str(mode_attr_val))
                sys.exit(1)

        # Check newly appended sub_modes, remove 'self' and duplicates
        sub_modes = self.get_sub_modes()

        if sub_modes != []:
            new_sub_modes = []
            for sub_mode in sub_modes:
                if self.name != sub_mode and sub_mode not in new_sub_modes:
                    new_sub_modes.append(sub_mode)
            self.set_sub_modes(new_sub_modes)
        return True

    @staticmethod
    def create_modes(ModeType, mdicts):
        '''
        Create modes of type ModeType from a given list of raw dicts
        Process dependencies.
        Return a list of modes objects.
        '''

        def merge_sub_modes(mode, parent, objs):
            # Check if there are modes available to merge
            sub_modes = mode.get_sub_modes()
            if sub_modes == []:
                return

            # Set parent if it is None. If not, check cyclic dependency
            if parent is None:
                parent = mode
            else:
                if mode.name == parent.name:
                    log.error("Cyclic dependency when processing mode \"%s\"",
                              mode.name)
                    sys.exit(1)

            for sub_mode in sub_modes:
                # Find the sub_mode obj from str
                found = False
                for obj in objs:
                    if sub_mode == obj.name:
                        # First recursively merge the sub_modes
                        merge_sub_modes(obj, parent, objs)

                        # Now merge the sub mode with mode
                        mode.merge_mode(obj)
                        found = True
                        break
                if not found:
                    log.error(
                        "Sub mode \"%s\" added to mode \"%s\" was not found!",
                        sub_mode, mode.name)
                    sys.exit(1)

        modes_objs = []
        # create a default mode if available
        default_mode = ModeType.get_default_mode()
        if default_mode is not None:
            modes_objs.append(default_mode)

        # Process list of raw dicts that represent the modes
        # Pass 1: Create unique set of modes by merging modes with the same name
        for mdict in mdicts:
            # Create a new item
            new_mode_merged = False
            new_mode = ModeType(mdict)
            for mode in modes_objs:
                # Merge new one with existing if available
                if mode.name == new_mode.name:
                    mode.merge_mode(new_mode)
                    new_mode_merged = True
                    break

            # Add the new mode to the list if not already appended
            if not new_mode_merged:
                modes_objs.append(new_mode)
                ModeType.item_names.append(new_mode.name)

        # Pass 2: Recursively expand sub modes within parent modes
        for mode in modes_objs:
            merge_sub_modes(mode, None, modes_objs)

        # Return the list of objects
        return modes_objs

    @staticmethod
    def get_default_mode(ModeType):
        return None

    @staticmethod
    def find_mode(mode_name, modes):
        '''
        Given a mode_name in string, go through list of modes and return the mode with
        the string that matches. Thrown an error and return None if nothing was found.
        '''
        for mode in modes:
            if mode_name == mode.name:
                return mode
        return None

    @staticmethod
    def find_and_merge_modes(mode, mode_names, modes, merge_modes=True):
        '''
        '''
        found_mode_objs = []
        for mode_name in mode_names:
            sub_mode = Modes.find_mode(mode_name, modes)
            if sub_mode is not None:
                found_mode_objs.append(sub_mode)
                if merge_modes is True:
                    mode.merge_mode(sub_mode)
            else:
                log.error("Mode \"%s\" enabled within mode \"%s\" not found!",
                          mode_name, mode.name)
                sys.exit(1)
        return found_mode_objs


class BuildModes(Modes):
    """
    Build modes.
    """

    # Maintain a list of build_modes str
    item_names = []

    def __init__(self, bdict):
        self.name = ""
        self.type = "build"
        if not hasattr(self, "mname"):
            self.mname = "mode"
        self.is_sim_mode = 0
        self.pre_build_cmds = []
        self.post_build_cmds = []
        self.en_build_modes = []
        self.build_opts = []
        self.build_timeout_mins = None
        self.pre_run_cmds = []
        self.post_run_cmds = []
        self.run_opts = []
        self.sw_images = []
        self.sw_build_opts = []

        super().__init__(bdict)
        self.en_build_modes = list(set(self.en_build_modes))

    @staticmethod
    def get_default_mode():
        return BuildModes({"name": "default"})


class RunModes(Modes):
    """
    Run modes.
    """

    # Maintain a list of run_modes str
    item_names = []

    def __init__(self, rdict):
        self.name = ""
        self.type = "run"
        if not hasattr(self, "mname"):
            self.mname = "mode"
        self.reseed = None
        self.pre_run_cmds = []
        self.post_run_cmds = []
        self.en_run_modes = []
        self.run_opts = []
        self.uvm_test = ""
        self.uvm_test_seq = ""
        self.build_mode = ""
        self.run_timeout_mins = None
        self.sw_images = []
        self.sw_build_device = ""
        self.sw_build_opts = []

        super().__init__(rdict)
        self.en_run_modes = list(set(self.en_run_modes))

    @staticmethod
    def get_default_mode():
        return None


class Tests(RunModes):
    """
    Abstraction for tests. The RunModes abstraction can be reused here with a few
    modifications.
    """

    # Maintain a list of tests str
    item_names = []

    # TODO: This info should be passed via hjson
    defaults = {
        "reseed": None,
        "uvm_test": "",
        "uvm_test_seq": "",
        "build_mode": "",
        "sw_images": [],
        "sw_build_device": "",
        "sw_build_opts": [],
        "run_timeout_mins": None
    }

    def __init__(self, tdict):
        if not hasattr(self, "mname"):
            self.mname = "test"
        super().__init__(tdict)

    @staticmethod
    def create_tests(tdicts, sim_cfg):
        '''
        Create Tests from a given list of raw dicts.
        TODO: enhance the raw dict to include file scoped defaults.
        Process enabled run modes and the set build mode.
        Return a list of test objects.
        '''

        def get_pruned_en_run_modes(test_en_run_modes, global_en_run_modes):
            pruned_en_run_modes = []
            for test_en_run_mode in test_en_run_modes:
                if test_en_run_mode not in global_en_run_modes:
                    pruned_en_run_modes.append(test_en_run_mode)
            return pruned_en_run_modes

        tests_objs = []
        # Pass 1: Create unique set of tests by merging tests with the same name
        for tdict in tdicts:
            # Create a new item
            new_test_merged = False
            new_test = Tests(tdict)
            for test in tests_objs:
                # Merge new one with existing if available
                if test.name == new_test.name:
                    test.merge_mode(new_test)
                    new_test_merged = True
                    break

            # Add the new test to the list if not already appended
            if not new_test_merged:
                tests_objs.append(new_test)
                Tests.item_names.append(new_test.name)

        # Pass 2: Process dependencies
        build_modes = []
        if hasattr(sim_cfg, "build_modes"):
            build_modes = getattr(sim_cfg, "build_modes")

        run_modes = []
        if hasattr(sim_cfg, "run_modes"):
            run_modes = getattr(sim_cfg, "run_modes")

        attrs = Tests.defaults
        for test_obj in tests_objs:
            # Unpack run_modes first
            en_run_modes = get_pruned_en_run_modes(test_obj.en_run_modes,
                                                   sim_cfg.en_run_modes)
            Modes.find_and_merge_modes(test_obj, en_run_modes, run_modes)

            # Find and set the missing attributes from sim_cfg
            # If not found in sim_cfg either, then throw a warning
            # TODO: These should be file-scoped
            for attr in attrs.keys():
                # Check if attr value is default
                val = getattr(test_obj, attr)
                default_val = attrs[attr]
                if val == default_val:
                    global_val = None
                    # Check if we can find a default in sim_cfg
                    if hasattr(sim_cfg, attr):
                        global_val = getattr(sim_cfg, attr)

                    if global_val is not None and global_val != default_val:
                        setattr(test_obj, attr, global_val)

            # Unpack the build mode for this test
            build_mode_objs = Modes.find_and_merge_modes(test_obj,
                                                         [test_obj.build_mode],
                                                         build_modes,
                                                         merge_modes=False)
            test_obj.build_mode = build_mode_objs[0]

            # Error if set build mode is actually a sim mode
            if test_obj.build_mode.is_sim_mode is True:
                log.error(
                    "Test \"%s\" uses build_mode %s which is actually a sim mode",
                    test_obj.name, test_obj.build_mode.name)
                sys.exit(1)

            # Merge build_mode's params with self
            test_obj.pre_run_cmds.extend(test_obj.build_mode.pre_run_cmds)
            test_obj.post_run_cmds.extend(test_obj.build_mode.post_run_cmds)
            test_obj.run_opts.extend(test_obj.build_mode.run_opts)
            test_obj.sw_images.extend(test_obj.build_mode.sw_images)
            test_obj.sw_build_opts.extend(test_obj.build_mode.sw_build_opts)

        # Return the list of tests
        return tests_objs

    @staticmethod
    def merge_global_opts(tests, global_pre_build_cmds, global_post_build_cmds,
                          global_build_opts, global_pre_run_cmds,
                          global_post_run_cmds, global_run_opts,
                          global_sw_images, global_sw_build_opts):
        processed_build_modes = set()
        for test in tests:
            if test.build_mode.name not in processed_build_modes:
                test.build_mode.pre_build_cmds.extend(global_pre_build_cmds)
                test.build_mode.post_build_cmds.extend(global_post_build_cmds)
                test.build_mode.build_opts.extend(global_build_opts)
                processed_build_modes.add(test.build_mode.name)
            test.pre_run_cmds.extend(global_pre_run_cmds)
            test.post_run_cmds.extend(global_post_run_cmds)
            test.run_opts.extend(global_run_opts)
            test.sw_images.extend(global_sw_images)
            test.sw_build_opts.extend(global_sw_build_opts)


class Regressions(Modes):
    """
    Abstraction for test sets / regression sets.
    """

    # Maintain a list of tests str
    item_names = []

    # TODO: define __repr__ and __str__ to print list of tests if VERBOSE

    def __init__(self, regdict):
        self.name = ""
        self.type = ""
        if not hasattr(self, "mname"):
            self.mname = "regression"

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
        super().__init__(regdict)

    @staticmethod
    def create_regressions(regdicts, sim_cfg, tests):
        '''
        Create Test sets from a given list of raw dicts.
        Return a list of test set objects.
        '''

        regressions_objs = []
        # Pass 1: Create unique set of test sets by merging test sets with the same name
        for regdict in regdicts:
            # Create a new item
            new_regression_merged = False
            new_regression = Regressions(regdict)

            # Check for name conflicts with tests before merging
            if new_regression.name in Tests.item_names:
                log.error(
                    "Test names and regression names are required to be unique. "
                    "The regression \"%s\" bears the same name with an existing test. ",
                    new_regression.name)
                sys.exit(1)

            for regression in regressions_objs:
                # Merge new one with existing if available
                if regression.name == new_regression.name:
                    regression.merge_mode(new_regression)
                    new_regression_merged = True
                    break

            # Add the new test to the list if not already appended
            if not new_regression_merged:
                regressions_objs.append(new_regression)
                Regressions.item_names.append(new_regression.name)

        # Pass 2: Process dependencies
        build_modes = []
        if hasattr(sim_cfg, "build_modes"):
            build_modes = getattr(sim_cfg, "build_modes")

        run_modes = []
        if hasattr(sim_cfg, "run_modes"):
            run_modes = getattr(sim_cfg, "run_modes")

        for regression_obj in regressions_objs:
            # Unpack the sim modes
            found_sim_mode_objs = Modes.find_and_merge_modes(
                regression_obj, regression_obj.en_sim_modes, build_modes,
                False)

            for sim_mode_obj in found_sim_mode_objs:
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
            found_run_mode_objs = Modes.find_and_merge_modes(
                regression_obj, regression_obj.en_run_modes, run_modes, False)

            # Only merge the pre_run_cmds, post_run_cmds & run_opts from the
            # run_modes enabled
            for run_mode_obj in found_run_mode_objs:
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
                regression_obj.test_names = Tests.item_names

            else:
                tests_objs = set()
                regression_obj.test_names = regression_obj.tests
                for test in regression_obj.tests:
                    test_obj = Modes.find_mode(test, sim_cfg.tests)
                    if test_obj is None:
                        log.error(
                            "Test \"%s\" added to regression \"%s\" not found!",
                            test, regression_obj.name)
                        continue
                    tests_objs.add(test_obj)
                regression_obj.tests = list(tests_objs)

        # Return the list of tests
        return regressions_objs

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
