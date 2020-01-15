#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""
Class describing simulation configuration object
"""

import datetime
import logging as log
import pprint
import re
import sys

import hjson

from testplanner import class_defs, testplan_utils

from .Deploy import *
from .Modes import *
from .utils import *


class SimCfg():
    """Simulation configuration object

    A simulation configuration class holds key information required for building a DV
    regression framework.
    """

    # Maintain a list of registered top level cfgs
    cfgs = []

    # Static variables - indicate timestamp.
    ts_format_long = "%A %B %d %Y %I:%M:%S%p %Z"
    ts_format = "%a.%m.%d.%y__%I.%M.%S%p"

    def __str__(self):
        return pprint.pformat(self.__dict__)

    def __repr__(self):
        return pprint.pformat(self.__dict__)

    def __init__(self, proj_root, args):
        # Options set from command line
        self.cfg_files = []
        self.cfg_files.append(args.cfg)
        self.items = args.items
        self.list_items = args.list
        self.simulator = args.simulator
        self.proj_root = proj_root
        self.scratch_root = args.scratch_root
        self.branch = args.branch
        self.build_opts = args.build_opts
        self.en_build_modes = args.build_modes
        self.run_opts = args.run_opts
        self.en_run_modes = args.run_modes
        self.build_unique = args.build_unique
        self.build_only = args.build_only
        self.run_only = args.run_only
        self.reseed_ovrd = args.reseed
        self.reseed_multiplier = args.reseed_multiplier
        self.waves = args.waves
        self.dump = args.dump
        self.max_waves = args.max_waves
        self.cov = args.cov
        self.profile = args.profile
        self.xprop_off = args.xprop_off
        self.no_rerun = args.no_rerun
        self.verbosity = "{" + args.verbosity + "}"
        self.email = args.email
        self.verbose = args.verbose
        self.dry_run = args.dry_run
        self.skip_ral = args.skip_ral
        self.job_prefix = args.job_prefix
        self.map_full_testplan = args.map_full_testplan

        # Set default sim modes for unpacking
        if self.waves is True: self.en_build_modes.append("waves")
        if self.cov is True: self.en_build_modes.append("cov")
        if self.profile is not 'none': self.en_build_modes.append("profile")
        if self.xprop_off is not True: self.en_build_modes.append("xprop")

        # Options built from cfg_file files
        self.project = ""
        self.flow = ""
        self.flow_makefile = ""
        self.scratch_path = ""
        self.build_dir = ""
        self.run_dir = ""
        self.sw_build_dir = ""
        self.pass_patterns = []
        self.fail_patterns = []
        self.name = ""
        self.dut = ""
        self.tb = ""
        self.testplan = ""
        self.fusesoc_core = ""
        self.ral_spec = ""
        self.build_modes = []
        self.run_modes = []
        self.regressions = []

        # Options from simulators - for building and running tests
        self.build_cmd = ""
        self.build_ex = ""
        self.flist_gen_cmd = ""
        self.flist_gen_opts = []
        self.flist_file = ""
        self.run_cmd = ""
        self.dump_file = ""
        self.exports = []

        # Register the seeds from command line with RunTest class.
        RunTest.seeds = args.seeds

        # Register the common deploy settings.
        Deploy.print_interval = args.print_interval
        Deploy.max_parallel = args.max_parallel
        Deploy.max_odirs = args.max_odirs

        # Current timestamp
        curr_ts = datetime.datetime.now()
        self.timestamp_long = curr_ts.strftime(SimCfg.ts_format_long)
        self.timestamp = curr_ts.strftime(SimCfg.ts_format)

        # Parse the cfg_file file tree
        self.parse_sim_cfg(args.cfg)

        # If build_unique is set, then add current timestamp to uniquify it
        if self.build_unique:
            self.build_dir += "_" + self.timestamp

        # Make substitutions, while ignoring the following wildcards
        # TODO: Find a way to set these in sim cfg instead
        ignored_wildcards = [
            "build_mode", "index", "test", "seed", "uvm_test", "uvm_test_seq"
        ]
        self.__dict__ = find_and_substitute_wildcards(self.__dict__,
                                                      self.__dict__,
                                                      ignored_wildcards)

        # Check if there are items to run
        if self.items == []:
            log.error(
                "No items provided for running this simulation / regression")
            sys.exit(1)

        # Use the default build mode for tests that do not specify it
        if not hasattr(self, "build_mode"):
            setattr(self, "build_mode", "default")

        self.process_exports()

        # Create objects from raw dicts - build_modes, sim_modes, run_modes,
        # tests and regressions
        self.create_objects()

        # Look at list of items and build the list of tests to run
        self.deploy = []
        self.build_list = []
        self.run_list = []
        self.create_build_and_run_list()

        # Create deploy objects
        self.create_deploy_objects()

        # Print info
        log.info("Scratch path: %s", self.scratch_path)

        # Register self
        SimCfg.cfgs.append(self)

    def do_purge(self):
        if self.scratch_path is not "":
            try:
                log.info("Purging scratch path %s", self.scratch_path)
                os.system("/bin/rm -rf " + self.scratch_path)
            except IOError:
                log.error('Failed to purge scratch directory %s',
                          self.scratch_path)

            # TODO: can't exit here!
            sys.exit(0)

    def process_exports(self):
        # Convert 'exports' to dict
        exports_dict = {}
        if self.exports != []:
            for item in self.exports:
                if type(item) is dict:
                    exports_dict.update(item)
                elif type(item) is str:
                    [key, value] = item.split(':', 1)
                    if type(key) is not str: key = str(key)
                    if type(value) is not str: value = str(value)
                    exports_dict.update({key.strip(): value.strip()})
                else:
                    log.error("Type error in \"exports\": %s", str(item))
                    sys.exit(1)
        self.exports = exports_dict

    def parse_sim_cfg(self, sim_cfg_file):
        try:
            log.debug("Parsing %s", sim_cfg_file)
            f = open(sim_cfg_file, 'rU')
            text = f.read()
            f.close()
        except:
            log.fatal("Failed to parse \"%s\"", sim_cfg_file)
            sys.exit(1)
        self.resolve_hjson_raw(hjson.loads(text, use_decimal=True))

    def resolve_hjson_raw(self, hjson_dict):
        attrs = self.__dict__.keys()
        rm_hjson_dict_keys = []
        import_cfgs = []
        for key in hjson_dict.keys():
            if key in attrs:
                hjson_dict_val = hjson_dict[key]
                self_val = getattr(self, key)
                scalar_types = {str: [""], int: [0, -1], bool: [False]}

                # Case 1: key value in class and hjson_dict differ - error!
                if type(hjson_dict_val) != type(self_val):
                    log.error("Coflicting key types: \"%s\" {\"%s, \"%s\"}",
                              key,
                              type(hjson_dict_val).__name__,
                              type(self_val).__name__)
                    sys.exit(1)

                # Case 2: key value in class and hjson_dict are strs - set if
                # not already set, else error!
                elif type(hjson_dict_val) in scalar_types.keys():
                    defaults = scalar_types[type(hjson_dict_val)]
                    if self_val == hjson_dict_val:
                        rm_hjson_dict_keys.append(key)
                    elif self_val in defaults and not hjson_dict_val in defaults:
                        setattr(self, key, hjson_dict_val)
                        rm_hjson_dict_keys.append(key)
                    elif not self_val in defaults and not hjson_dict_val in defaults:
                        log.error(
                            "Coflicting values {\"%s\", \"%s\"} encountered for key \"%s\"",
                            str(self_val), str(hjson_dict_val), key)
                        sys.exit(1)

                # Case 3: key value in class and hjson_dict are lists - merge'em
                elif type(hjson_dict_val) is list and type(self_val) is list:
                    self_val.extend(hjson_dict_val)
                    setattr(self, key, self_val)
                    rm_hjson_dict_keys.append(key)

                # Case 4: unknown issue
                else:
                    log.error(
                        "Type of \"%s\" (%s) in %s appears to be invalid (should be %s)",
                        key,
                        type(hjson_dict_val).__name__, hjson_dict,
                        type(self_val).__name__)
                    sys.exit(1)
            # If key is 'import_cfgs' then add to the list of sim_cfgs to
            # process
            elif key == 'import_cfgs':
                import_cfgs.extend(hjson_dict[key])
                rm_hjson_dict_keys.append(key)

            else:
                # add key-value to class
                setattr(self, key, hjson_dict[key])
                rm_hjson_dict_keys.append(key)

        # Parse imported sim_cfgs
        for cfg_file in import_cfgs:
            if not cfg_file in self.cfg_files:
                self.cfg_files.append(cfg_file)
                # Substitute wildcards in cfg_file files since we need to process
                # them right away.
                cfg_file = subst_wildcards(cfg_file, self.__dict__)
                self.parse_sim_cfg(cfg_file)
            else:
                log.error("Sim cfg file \"%s\" has already been parsed",
                          cfg_file)

    def create_objects(self):
        # Create build and run modes objects
        build_modes = Modes.create_modes(BuildModes,
                                         getattr(self, "build_modes"))
        setattr(self, "build_modes", build_modes)

        run_modes = Modes.create_modes(RunModes, getattr(self, "run_modes"))
        setattr(self, "run_modes", run_modes)

        # Walk through build modes enabled on the CLI and append the opts
        for en_build_mode in self.en_build_modes:
            build_mode_obj = Modes.find_mode(en_build_mode, build_modes)
            if build_mode_obj is not None:
                self.build_opts.extend(build_mode_obj.build_opts)
                self.run_opts.extend(build_mode_obj.run_opts)
            else:
                log.error(
                    "Mode \"%s\" enabled on the the command line is not defined",
                    en_build_mode)
                sys.exit(1)

        # Walk through run modes enabled on the CLI and append the opts
        for en_run_mode in self.en_run_modes:
            run_mode_obj = Modes.find_mode(en_run_mode, run_modes)
            if run_mode_obj is not None:
                self.run_opts.extend(run_mode_obj.run_opts)
            else:
                log.error(
                    "Mode \"%s\" enabled on the the command line is not defined",
                    en_run_mode)
                sys.exit(1)

        # Create tests from given list of items
        tests = Tests.create_tests(getattr(self, "tests"), self)
        setattr(self, "tests", tests)

        # Create regressions
        regressions = Regressions.create_regressions(
            getattr(self, "regressions"), self, tests)
        setattr(self, "regressions", regressions)

    def print_list(self):
        for list_item in self.list_items:
            if hasattr(self, list_item):
                items = getattr(self, list_item)
                for item in items:
                    log.info(item)
            else:
                log.error("Item %s does not exist!", list_item)

    def create_build_and_run_list(self):
        # Walk through the list of items to run and create the build and run
        # objects.
        # Allow multiple regressions to run as long as the do not enable
        # sim_modes or run_modes
        def get_overlapping_tests(tests, run_list_names):
            overlapping_tests = []
            for test in tests:
                if test.name in run_list_names:
                    overlapping_tests.append(test)
            return overlapping_tests

        def prune_items(items, marked_items):
            pruned_items = []
            for item in items:
                if item not in marked_items: pruned_items.append(item)
            return pruned_items

        items_list = self.items
        run_list_names = []
        marked_items = []
        # Process regressions first
        for regression in self.regressions:
            if regression.name in items_list:
                overlapping_tests = get_overlapping_tests(
                    regression.tests, run_list_names)
                if overlapping_tests != []:
                    log.error("Regression \"%s\" added for run contains tests that overlap with " + \
                              "other regressions added. This can result in conflicting " + \
                              "build / run_opts to be set causing unexpected results.",
                              regression.name)
                    sys.exit(1)

                self.run_list.extend(regression.tests)
                # Merge regression's build and run opts with its tests and their
                # build_modes
                regression.merge_regression_opts()
                run_list_names.extend(regression.test_names)
                marked_items.append(regression.name)
        items_list = prune_items(items_list, marked_items)

        # Process individual tests
        for test in self.tests:
            if test.name in items_list:
                overlapping_tests = get_overlapping_tests([test],
                                                          run_list_names)
                if overlapping_tests == []:
                    self.run_list.append(test)
                    run_list_names.append(test.name)
                    marked_items.append(test.name)
        items_list = prune_items(items_list, marked_items)

        # Merge the global build and run opts
        Tests.merge_global_opts(self.run_list, self.build_opts, self.run_opts)

        # Check if all items has been processed
        if items_list != []:
            log.error("The items %s added for run were not found! Use the --list switch " + \
                      "to see a list of available tests / regressions for run", items_list)
            sys.exit(1)

        # Process reseed override and create the build_list
        build_list_names = []
        for test in self.run_list:
            # Override reseed if available.
            if self.reseed_ovrd != -1:
                test.reseed = self.reseed_ovrd

            # Apply reseed multiplier if set on the command line.
            test.reseed *= self.reseed_multiplier

            # Create the unique set of builds needed.
            if test.build_mode.name not in build_list_names:
                self.build_list.append(test.build_mode)
                build_list_names.append(test.build_mode.name)

    def create_deploy_objects(self):
        builds = []
        build_map = {}
        for build in self.build_list:
            item = CompileSim(build, self)
            builds.append(item)
            build_map[build] = item

        runs = []
        for test in self.run_list:
            for num in range(test.reseed):
                item = RunTest(num, test, self)
                if self.build_only is False:
                    build_map[test.build_mode].sub.append(item)
                runs.append(item)

        if self.run_only is True:
            self.deploy = runs
        else:
            self.deploy = builds

    def gen_results(self, fmt="md"):
        '''
        The function is called after the regression has completed. It collates the status of
        all run targets and generates a dict. It parses the testplan and maps the generated
        result to the testplan entries to generate a final table (list). It uses the fmt arg
        to dump the final result as a markdown of html.
        '''

        # TODO: add support for html
        def retrieve_result(name, results):
            for item in results:
                if name == item["name"]: return item
            return None

        def gen_results_sub(items, results):
            '''
            Generate the results table from the test runs (builds are ignored).
            The table has 3 columns - name, passing and total as a list of dicts.
            This is populated for all tests. The number of passing and total is
            in reference to the number of iterations or reseeds for that test.
            This list of dicts is directly consumed by the Testplan::results_table
            method for testplan mapping / annotation.
            '''
            if items == []: return results
            for item in items:
                # Only generate results table for runs.
                if item.target == "run":
                    result = retrieve_result(item.name, results)
                    if result is None:
                        result = {"name": item.name, "passing": 0, "total": 0}
                        results.append(result)
                    if item.status == "P": result["passing"] += 1
                    result["total"] += 1
                results = gen_results_sub(item.sub, results)
            return results

        # Generate results table for runs.
        results_str = "# " + self.name.upper() + " Regression Results\n"
        results_str += "  Run on " + self.timestamp_long + "\n"
        results_str += "\n## Test Results\n"
        testplan = testplan_utils.parse_testplan(self.testplan)
        results_str += testplan.results_table(
            regr_results=gen_results_sub(self.deploy, []),
            map_full_testplan=self.map_full_testplan)

        # Write results to the scratch area
        regr_results_file = self.scratch_path + "/regr_results_" + self.timestamp + "." + fmt
        f = open(regr_results_file, 'w')
        f.write(results_str)
        f.close()
        return results_str
