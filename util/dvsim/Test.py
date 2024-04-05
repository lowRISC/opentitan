# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from copy import deepcopy
import logging as log
import sys

from modes import RunMode, find_and_merge_modes


class Test(RunMode):
    """
    Abstraction for a test. The RunMode abstraction can be reused here with a few
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
        "run_timeout_mins": None,
        "run_timeout_multiplier": None
    }

    @staticmethod
    def create_tests(tdicts, sim_cfg):
        '''
        Create Test objects from a given list of raw dicts.
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
            new_test = Test(tdict)
            for test in tests_objs:
                # Merge new one with existing if available
                if test.name == new_test.name:
                    test.merge_mode(new_test)
                    new_test_merged = True
                    break

            # Add the new test to the list if not already appended
            if not new_test_merged:
                tests_objs.append(new_test)
                Test.item_names.append(new_test.name)

        # Pass 2: Process dependencies
        build_modes = getattr(sim_cfg, "build_modes", [])
        run_modes = getattr(sim_cfg, "run_modes", [])

        attrs = Test.defaults
        for test_obj in tests_objs:
            # Unpack run_modes first
            en_run_modes = get_pruned_en_run_modes(test_obj.en_run_modes,
                                                   sim_cfg.en_run_modes)
            find_and_merge_modes(test_obj, en_run_modes, run_modes)

            # Find and set the missing attributes from sim_cfg
            # If not found in sim_cfg either, then throw a warning
            # TODO: These should be file-scoped
            for attr in attrs.keys():
                # Check if attr value is default
                val = getattr(test_obj, attr)
                default_val = attrs[attr]
                if val == default_val:
                    # If sim_cfg specifies a value for this attribute and this
                    # value isn't equal to default_val, then copy the sim_cfg
                    # value across to the test object.
                    global_val = getattr(sim_cfg, attr, None)
                    if global_val is not None and global_val != default_val:

                        # TODO: This is a workaround for a memory usage bug
                        # that triggered issue #20550. It's a pretty hacky
                        # solution! We should probably tidy this up properly.
                        setattr(test_obj, attr, deepcopy(global_val))

            # Unpack the build mode for this test
            build_mode_objs = find_and_merge_modes(test_obj,
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
