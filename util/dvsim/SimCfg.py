# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""
Class describing simulation configuration object
"""

import logging as log
import sys
from collections import OrderedDict

from Deploy import *
from FlowCfg import FlowCfg
from Modes import *
from testplanner import class_defs, testplan_utils
from utils import *


class SimCfg(FlowCfg):
    """Simulation configuration object

    A simulation configuration class holds key information required for building a DV
    regression framework.
    """
    def __init__(self, flow_cfg_file, proj_root, args):
        super().__init__(flow_cfg_file, proj_root, args)
        # Options set from command line
        self.tool = args.tool
        self.build_opts = []
        self.build_opts.extend(args.build_opts)
        self.en_build_modes = []
        self.en_build_modes.extend(args.build_modes)
        self.run_opts = []
        self.run_opts.extend(args.run_opts)
        self.en_run_modes = []
        self.en_run_modes.extend(args.run_modes)
        self.build_unique = args.build_unique
        self.build_only = args.build_only
        self.run_only = args.run_only
        self.reseed_ovrd = args.reseed
        self.reseed_multiplier = args.reseed_multiplier
        self.waves = args.waves
        self.dump = args.dump
        self.max_waves = args.max_waves
        self.cov = args.cov
        self.cov_merge_previous = args.cov_merge_previous
        self.profile = args.profile
        self.xprop_off = args.xprop_off
        self.no_rerun = args.no_rerun
        self.verbosity = "{" + args.verbosity + "}"
        self.email = args.email
        self.verbose = args.verbose
        self.dry_run = args.dry_run
        self.map_full_testplan = args.map_full_testplan

        # Disable cov if --build-only is passed.
        if self.build_only: self.cov = False

        # Set default sim modes for unpacking
        if self.waves is True: self.en_build_modes.append("waves")
        if self.cov is True: self.en_build_modes.append("cov")
        if self.profile != 'none': self.en_build_modes.append("profile")
        if self.xprop_off is not True: self.en_build_modes.append("xprop")

        # Options built from cfg_file files
        self.project = ""
        self.flow = ""
        self.flow_makefile = ""
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

        # Options from tools - for building and running tests
        self.build_cmd = ""
        self.flist_gen_cmd = ""
        self.flist_gen_opts = []
        self.flist_file = ""
        self.run_cmd = ""
        self.dump_file = ""

        # Generated data structures
        self.links = {}
        self.build_list = []
        self.run_list = []
        self.cov_merge_deploy = None
        self.cov_report_deploy = None
        self.results_summary = OrderedDict()

        # If is_master_cfg is set, then each cfg will have its own cov_deploy.
        # Maintain an array of those in cov_deploys.
        self.cov_deploys = []

        # Parse the cfg_file file tree
        self.parse_flow_cfg(flow_cfg_file)
        self._post_parse_flow_cfg()

        # If build_unique is set, then add current timestamp to uniquify it
        if self.build_unique:
            self.build_dir += "_" + self.timestamp

        # Process overrides before substituting the wildcards.
        self._process_overrides()

        # Make substitutions, while ignoring the following wildcards
        # TODO: Find a way to set these in sim cfg instead
        ignored_wildcards = [
            "build_mode", "index", "test", "seed", "uvm_test", "uvm_test_seq",
            "cov_db_dirs", "sw_dir", "sw_name", "sw_build_device"
        ]
        self.__dict__ = find_and_substitute_wildcards(self.__dict__,
                                                      self.__dict__,
                                                      ignored_wildcards,
                                                      self.is_master_cfg)

        # Set the title for simulation results.
        self.results_title = self.name.upper() + " Simulation Results"

        # Stuff below only pertains to individual cfg (not master cfg)
        # or individual selected cfgs (if select_cfgs is configured via command line)
        # TODO: find a better way to support select_cfgs
        if not self.is_master_cfg and (not self.select_cfgs or self.name in self.select_cfgs):
            # Print info:
            log.info("[scratch_dir]: [%s]: [%s]", self.name, self.scratch_path)

            # Set directories with links for ease of debug / triage.
            self.links = {
                "D": self.scratch_path + "/" + "dispatched",
                "P": self.scratch_path + "/" + "passed",
                "F": self.scratch_path + "/" + "failed",
                "K": self.scratch_path + "/" + "killed"
            }

            # Use the default build mode for tests that do not specify it
            if not hasattr(self, "build_mode"):
                setattr(self, "build_mode", "default")

            self._process_exports()

            # Create objects from raw dicts - build_modes, sim_modes, run_modes,
            # tests and regressions, only if not a master cfg obj
            self._create_objects()

        # Post init checks
        self.__post_init__()

    def __post_init__(self):
        # Run some post init checks
        super().__post_init__()

    @staticmethod
    def create_instance(flow_cfg_file, proj_root, args):
        '''Create a new instance of this class as with given parameters.
        '''
        return SimCfg(flow_cfg_file, proj_root, args)

    def kill(self):
        '''kill running processes and jobs gracefully
        '''
        super().kill()
        for item in self.cov_deploys:
            item.kill()

    # Purge the output directories. This operates on self.
    def _purge(self):
        if self.scratch_path:
            try:
                log.info("Purging scratch path %s", self.scratch_path)
                os.system("/bin/rm -rf " + self.scratch_path)
            except IOError:
                log.error('Failed to purge scratch directory %s',
                          self.scratch_path)

    def _create_objects(self):
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

        # Regressions
        # Parse testplan if provided.
        if self.testplan != "":
            self.testplan = testplan_utils.parse_testplan(self.testplan)
            # Extract tests in each milestone and add them as regression target.
            self.regressions.extend(self.testplan.get_milestone_regressions())

        # Create regressions
        regressions = Regressions.create_regressions(
            getattr(self, "regressions"), self, tests)
        setattr(self, "regressions", regressions)

    def _print_list(self):
        for list_item in self.list_items:
            log.info("---- List of %s in %s ----", list_item, self.name)
            if hasattr(self, list_item):
                items = getattr(self, list_item)
                for item in items:
                    log.info(item)
            else:
                log.error("Item %s does not exist!", list_item)

    def _create_build_and_run_list(self):
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

        # Check if there are items to run
        if self.items == []:
            log.error(
                "No items provided for running this simulation / regression")
            sys.exit(1)

        items_list = self.items
        run_list_names = []
        marked_items = []
        # Process regressions first
        for regression in self.regressions:
            if regression.name in items_list:
                overlapping_tests = get_overlapping_tests(
                    regression.tests, run_list_names)
                if overlapping_tests != []:
                    log.error(
                        "Regression \"%s\" added for run contains tests that overlap with "
                        "other regressions added. This can result in conflicting "
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

        # Check if all items have been processed
        if items_list != []:
            log.error(
                "The items %s added for run were not found in \n%s!\n "
                "Use the --list switch to see a list of available "
                "tests / regressions.", items_list, self.flow_cfg_file)

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

    def _create_dirs(self):
        '''Create initial set of directories
        '''
        # Invoking system calls has a performance penalty.
        # Construct a single command line chained with '&&' to invoke
        # the system call only once, rather than multiple times.
        create_link_dirs_cmd = ""
        for link in self.links.keys():
            create_link_dirs_cmd += "/bin/rm -rf " + self.links[link] + " && "
            create_link_dirs_cmd += "mkdir -p " + self.links[link] + " && "
        create_link_dirs_cmd += " true"

        try:
            os.system(create_link_dirs_cmd)
        except IOError:
            log.error("Error running when running the cmd \"%s\"",
                      create_link_dirs_cmd)
            sys.exit(1)

    def _create_deploy_objects(self):
        '''Create deploy objects from the build and run lists.
        '''

        # Create the build and run list first
        self._create_build_and_run_list()

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

        self.builds = builds
        self.runs = runs
        if self.run_only is True:
            self.deploy = runs
        else:
            self.deploy = builds

        # Create cov_merge and cov_report objects
        if self.cov:
            self.cov_merge_deploy = CovMerge(self)
            self.cov_report_deploy = CovReport(self)
            # Generate reports only if merge was successful; add it as a dependency
            # of merge.
            self.cov_merge_deploy.sub.append(self.cov_report_deploy)

        # Create initial set of directories before kicking off the regression.
        self._create_dirs()

    def create_deploy_objects(self):
        '''Public facing API for _create_deploy_objects().
        '''
        super().create_deploy_objects()

        # Also, create cov_deploys
        if self.cov:
            for item in self.cfgs:
                if item.cov:
                    self.cov_deploys.append(item.cov_merge_deploy)

    # deploy additional commands as needed. We do this separated for coverage
    # since that needs to happen at the end.
    def deploy_objects(self):
        '''This is a public facing API, so we use "self.cfgs" instead of self.
        '''
        # Invoke the base class method to run the regression.
        super().deploy_objects()

        # If coverage is enabled, then deploy the coverage tasks.
        if self.cov:
            Deploy.deploy(self.cov_deploys)

    def _cov_analyze(self):
        '''Use the last regression coverage data to open up the GUI tool to
        analyze the coverage.
        '''
        cov_analyze_deploy = CovAnalyze(self)
        self.deploy = [cov_analyze_deploy]

    def cov_analyze(self):
        '''Public facing API for analyzing coverage.
        '''
        for item in self.cfgs:
            item._cov_analyze()

    def _gen_results(self):
        '''
        The function is called after the regression has completed. It collates the
        status of all run targets and generates a dict. It parses the testplan and
        maps the generated result to the testplan entries to generate a final table
        (list). It also prints the full list of failures for debug / triage. If cov
        is enabled, then the summary coverage report is also generated. The final
        result is in markdown format.
        '''

        # TODO: add support for html
        def retrieve_result(name, results):
            for item in results:
                if name == item["name"]: return item
            return None

        def gen_results_sub(items, results, fail_msgs):
            '''
            Generate the results table from the test runs (builds are ignored).
            The table has 3 columns - name, passing and total as a list of dicts.
            This is populated for all tests. The number of passing and total is
            in reference to the number of iterations or reseeds for that test.
            This list of dicts is directly consumed by the Testplan::results_table
            method for testplan mapping / annotation.
            '''
            if items == []: return (results, fail_msgs)
            for item in items:
                if item.status == "F":
                    fail_msgs += item.fail_msg

                # Generate results table for runs.
                if item.target == "run":
                    result = retrieve_result(item.name, results)
                    if result is None:
                        result = {"name": item.name, "passing": 0, "total": 0}
                        results.append(result)
                    if item.status == "P": result["passing"] += 1
                    result["total"] += 1
                (results, fail_msgs) = gen_results_sub(item.sub, results,
                                                       fail_msgs)
            return (results, fail_msgs)

        regr_results = []
        fail_msgs = ""
        deployed_items = self.deploy
        if self.cov: deployed_items.append(self.cov_merge_deploy)
        (regr_results, fail_msgs) = gen_results_sub(deployed_items,
                                                    regr_results, fail_msgs)

        # Add title if there are indeed failures
        if fail_msgs != "":
            fail_msgs = "\n## List of Failures\n" + fail_msgs
            self.errors_seen = True

        # Generate results table for runs.
        results_str = "## " + self.results_title + "\n"
        results_str += "### " + self.timestamp_long + "\n"

        # Add path to testplan.
        testplan = "https://" + self.doc_server + '/' + self.rel_path
        testplan = testplan.replace("/dv", "/doc/dv_plan/#testplan")
        results_str += "### [Testplan](" + testplan + ")\n"
        results_str += "### Simulator: " + self.tool.upper() + "\n\n"

        if regr_results == []:
            results_str += "No results to display.\n"

        else:
            # TODO: check if testplan is not null?
            # Map regr results to the testplan entries.
            results_str += self.testplan.results_table(
                regr_results=regr_results,
                map_full_testplan=self.map_full_testplan)
            results_str += "\n"
            self.results_summary = self.testplan.results_summary

            # Append coverage results of coverage was enabled.
            if self.cov:
                if self.cov_report_deploy.status == "P":
                    results_str += "\n## Coverage Results\n"
                    # Link the dashboard page using "cov_report_page" value.
                    # TODO: hack to only link VCS generated results.
                    if self.tool == "vcs" and hasattr(self, "cov_report_page"):
                        results_str += "\n### [Coverage Dashboard]"
                        results_str += "({})\n\n".format(
                            getattr(self, "cov_report_page"))
                    results_str += self.cov_report_deploy.cov_results
                    self.results_summary[
                        "Coverage"] = self.cov_report_deploy.cov_total
                else:
                    self.results_summary["Coverage"] = "--"

            # append link of detail result to block name
            self.results_summary["Name"] = self._get_results_page_link(
                self.results_summary["Name"])

        # Append failures for triage
        self.results_md = results_str + fail_msgs
        results_str += fail_msgs

        # Write results to the scratch area
        results_file = self.scratch_path + "/results_" + self.timestamp + ".md"
        f = open(results_file, 'w')
        f.write(self.results_md)
        f.close()

        # Return only the tables
        log.info("[results page]: [%s] [%s]", self.name, results_file)
        return results_str

    def gen_results_summary(self):

        # sim summary result has 5 columns from each SimCfg.results_summary
        header = ["Name", "Passing", "Total", "Pass Rate"]
        if self.cov: header.append('Coverage')
        table = [header]
        colalign = ("center", ) * len(header)
        for item in self.cfgs:
            row = []
            for title in item.results_summary:
                row.append(item.results_summary[title])
            if row == []: continue
            table.append(row)
        self.results_summary_md = "## " + self.results_title + " (Summary)\n"
        self.results_summary_md += "### " + self.timestamp_long + "\n"
        self.results_summary_md += tabulate(table,
                                            headers="firstrow",
                                            tablefmt="pipe",
                                            colalign=colalign)
        print(self.results_summary_md)
        return self.results_summary_md

    def _publish_results(self):
        '''Publish coverage results to the opentitan web server.'''
        super()._publish_results()

        if self.cov:
            # TODO: hack to only allow VCS coverage data to be uploaded.
            if self.tool != "vcs": return
            results_server_dir_url = self.results_server_dir.replace(
                self.results_server_prefix, self.results_server_url_prefix)

            log.info("Publishing coverage results to %s",
                     results_server_dir_url)
            cmd = self.results_server_cmd + " -m cp -R " + \
                  self.cov_report_deploy.cov_report_dir + " " + self.results_server_dir
            try:
                cmd_output = subprocess.run(args=cmd,
                                            shell=True,
                                            stdout=subprocess.PIPE,
                                            stderr=subprocess.STDOUT)
                log.log(VERBOSE, cmd_output.stdout.decode("utf-8"))
            except Exception as e:
                log.error("%s: Failed to publish results:\n\"%s\"", e,
                          str(cmd))
