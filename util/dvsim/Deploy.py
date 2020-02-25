#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""
Classes
"""

import logging as log
import pprint
import random
import re
import shlex
import sys
import time

import hjson
from tabulate import tabulate

from .utils import *


class Deploy():
    """
    Abstraction for deploying builds and runs.
    """

    # Maintain a list of dispatched items.
    dispatch_counter = 0

    # Misc common deploy settings.
    print_interval = 5
    max_parallel = 16
    max_odirs = 5

    def __self_str__(self):
        if log.getLogger().isEnabledFor(VERBOSE):
            return pprint.pformat(self.__dict__)
        else:
            ret = self.cmd
            if self.sub != []: ret += "\nSub:\n" + str(self.sub)
            return ret

    def __str__(self):
        return self.__self_str__()

    def __repr__(self):
        return self.__self_str__()

    def __init__(self, sim_cfg):
        # Cross ref the whole cfg object for ease.
        self.sim_cfg = sim_cfg

        # Common vars
        self.cmd = ""
        self.odir = ""
        self.log = ""
        self.fail_msg = ""

        # Flag to indicate whether to 'overwrite' if odir already exists,
        # or to backup the existing one and create a new one.
        # For builds, we want to overwrite existing to leverage the tools'
        # incremental / partition compile features. For runs, we may want to
        # create a new one.
        self.renew_odir = False

        # List of vars required to be exported to sub-shell
        self.exports = {}

        # Deploy sub commands
        self.sub = []

        # Process
        self.process = None
        self.log_fd = None
        self.status = None

        # These are command, output directory and log file
        self.mandatory_misc_attrs.update({
            "name": False,
            "build_mode": False,
            "flow_makefile": False,
            "exports": False,
            "dry_run": False
        })

    # Function to parse a dict and extract the mandatory cmd and misc attrs.
    def parse_dict(self, ddict):
        if not hasattr(self, "target"):
            log.error(
                "Class %s does not have the mandatory attribute \"target\" defined",
                self.__class__.__name__)
            sys.exit(1)

        ddict_keys = ddict.keys()
        for key in self.mandatory_cmd_attrs.keys():
            if self.mandatory_cmd_attrs[key] == False:
                if key in ddict_keys:
                    setattr(self, key, ddict[key])
                    self.mandatory_cmd_attrs[key] = True

        for key in self.mandatory_misc_attrs.keys():
            if self.mandatory_misc_attrs[key] == False:
                if key in ddict_keys:
                    setattr(self, key, ddict[key])
                    self.mandatory_misc_attrs[key] = True

    def __post_init__(self):
        # Ensure all mandatory attrs are set
        for attr in self.mandatory_cmd_attrs.keys():
            if self.mandatory_cmd_attrs[attr] is False:
                log.error("Attribute \"%s\" not found for \"%s\".", attr,
                          self.name)
                sys.exit(1)

        for attr in self.mandatory_misc_attrs.keys():
            if self.mandatory_misc_attrs[attr] is False:
                log.error("Attribute \"%s\" not found for \"%s\".", attr,
                          self.name)
                sys.exit(1)

        # Recursively search and replace wildcards
        self.__dict__ = find_and_substitute_wildcards(self.__dict__,
                                                      self.__dict__)

        # Set the command, output dir and log
        self.odir = getattr(self, self.target + "_dir")
        # Set the output dir link name to the basename of odir (by default)
        self.odir_ln = os.path.basename(os.path.normpath(self.odir))
        self.log = self.odir + "/" + self.target + ".log"

        # If using LSF, redirect stdout and err to the log file
        self.cmd = self.construct_cmd()

    def construct_cmd(self):
        cmd = "make -f " + self.flow_makefile + " " + self.target
        if self.dry_run is True:
            cmd += " -n"
        for attr in self.mandatory_cmd_attrs.keys():
            value = getattr(self, attr)
            if type(value) is list:
                pretty_value = []
                for item in value:
                    pretty_value.append(item.strip())
                value = " ".join(pretty_value)
            if type(value) is bool:
                value = int(value)
            if type(value) is str:
                value = value.strip()
            cmd += " " + attr + "=\"" + str(value) + "\""

        # TODO: If not running locally, redirect stdout and err to the log file
        # self.cmd += " > " + self.log + " 2>&1 &"
        return cmd

    def dispatch_cmd(self):
        self.exports.update(os.environ)
        args = shlex.split(self.cmd)
        try:
            # If renew_odir flag is True - then move it.
            if self.renew_odir: self.odir_limiter(odir=self.odir)
            os.system("mkdir -p " + self.odir)
            os.system("ln -s " + self.odir + " " + self.sim_cfg.links['D'] +
                      '/' + self.odir_ln)
            f = open(self.log, "w")
            self.process = subprocess.Popen(args,
                                            bufsize=4096,
                                            universal_newlines=True,
                                            stdout=f,
                                            stderr=f,
                                            env=self.exports)
            self.log_fd = f
            self.status = "."
            Deploy.dispatch_counter += 1
        except IOError:
            log.error('IO Error: See %s', self.log)
            if self.log_fd: self.log_fd.close()
            self.status = "K"

    def odir_limiter(self, odir, max_odirs=-1):
        '''Function to backup previously run output directory to maintain a
        history of a limited number of output directories. It deletes the output
        directory with the oldest timestamps, if the limit is reached. It returns
        a list of directories that remain after deletion.
        Arguments:
        odir: The output directory to backup
        max_odirs: Maximum output directories to maintain as history.

        Returns:
        dirs: Space-separated list of directories that remain after deletion.
        '''
        try:
            # If output directory exists, back it up.
            if os.path.exists(odir):
                ts = run_cmd("date '+" + self.sim_cfg.ts_format + "' -d \"" +
                             "$(stat -c '%y' " + odir + ")\"")
                os.system('mv ' + odir + " " + odir + "_" + ts)
        except IOError:
            log.error('Failed to back up existing output directory %s', odir)

        dirs = ""
        # Delete older directories.
        try:
            pdir = os.path.realpath(odir + "/..")
            # Fatal out if pdir got set to root.
            if pdir == "/":
                log.fatal(
                    "Something went wrong while processing \"%s\": odir = \"%s\"",
                    self.name, odir)
                sys.exit(1)

            if os.path.exists(pdir):
                find_cmd = "find " + pdir + " -mindepth 1 -maxdepth 1 -type d "
                dirs = run_cmd(find_cmd)
                dirs = dirs.replace('\n', ' ')
                list_dirs = dirs.split()
                num_dirs = len(list_dirs)
                if max_odirs == -1: max_odirs = self.max_odirs
                num_rm_dirs = num_dirs - max_odirs
                if num_rm_dirs > -1:
                    rm_dirs = run_cmd(find_cmd +
                                      "-printf '%T+ %p\n' | sort | head -n " +
                                      str(num_rm_dirs + 1) +
                                      " | awk '{print $2}'")
                    rm_dirs = rm_dirs.replace('\n', ' ')
                    dirs = dirs.replace(rm_dirs, "")
                    os.system("/usr/bin/rm -rf " + rm_dirs)
        except IOError:
            log.error("Failed to delete old run directories!")
        return dirs

    def set_status(self):
        self.status = 'P'
        if self.dry_run is False:
            for fail_pattern in self.fail_patterns:
                grep_cmd = "grep -m 1 -E \'" + fail_pattern + "\' " + self.log
                (status, rslt) = subprocess.getstatusoutput(grep_cmd + " -c")
                if rslt != "0":
                    (status, rslt) = subprocess.getstatusoutput(grep_cmd)
                    msg = "```\n{}\n```\n".format(rslt)
                    self.fail_msg += msg
                    log.log(VERBOSE, msg)
                    self.status = 'F'
                    break

            # Return if status is fail - no need to look for pass patterns.
            if self.status == 'F': return

            # If fail patterns were not found, ensure pass patterns indeed were.
            for pass_pattern in self.pass_patterns:
                grep_cmd = "grep -c -m 1 -E \'" + pass_pattern + "\' " + self.log
                (status, rslt) = subprocess.getstatusoutput(grep_cmd)
                if rslt == "0":
                    msg = "Pass pattern \"{}\" not found.<br>\n".format(
                        pass_pattern)
                    self.fail_msg += msg
                    log.log(VERBOSE, msg)
                    self.status = 'F'
                    break

    # Recursively set sub-item's status if parent item fails
    def set_sub_status(self, status):
        if self.sub == []: return
        for sub_item in self.sub:
            sub_item.status = status
            sub_item.set_sub_status(status)

    def link_odir(self):
        if self.status == '.':
            log.error("Method unexpectedly called!")
        else:
            old_link = self.sim_cfg.links['D'] + "/" + self.odir_ln
            new_link = self.sim_cfg.links[self.status] + "/" + self.odir_ln
            cmd = "ln -s " + self.odir + " " + new_link + "; "
            cmd += "rm " + old_link
            try:
                os.system(cmd)
            except Exception as e:
                log.error("Cmd \"%s\" could not be run", cmd)

    def get_status(self):
        if self.status != ".": return
        if self.process.poll() is not None:
            self.log_fd.close()
            if self.process.returncode != 0:
                msg = "Last 10 lines of the log:<br>\n"
                self.fail_msg += msg
                log.log(VERBOSE, msg)
                get_fail_msg_cmd = "tail -n 10 " + self.log
                msg = run_cmd(get_fail_msg_cmd)
                msg = "```\n{}\n```\n".format(msg)
                self.fail_msg += msg
                log.log(VERBOSE, msg)
                self.status = "F"
            else:
                self.set_status()

            log.log(VERBOSE, "Item %s has completed execution: %s", self.name,
                    self.status)
            Deploy.dispatch_counter -= 1
            self.link_odir()
            del self.process

    @staticmethod
    def deploy(items):
        dispatched_items = []

        def dispatch_items(items):
            item_names = {}
            for item in items:
                if item.target not in item_names.keys():
                    item_names[item.target] = "["
                if item.status is None:
                    item_names[item.target] += "  "
                    if log.getLogger().isEnabledFor(VERBOSE):
                        item_names[
                            item.target] += item.name + ":" + item.log + ",\n"
                    else:
                        item_names[item.target] += item.odir_ln + ", "
                    item.dispatch_cmd()
                    dispatched_items.append(item)

            for target in item_names.keys():
                if item_names[target] != "[":
                    item_names[target] = " [" + item_names[target][3:]
                    item_names[target] = item_names[target][:-2] + "]"
                    log.info("[dvsim]: %s:\n%s", target, item_names[target])

        # Dispatch the given items
        dispatch_items_queue = []
        if len(items) > Deploy.max_parallel:
            dispatch_items(items[0:Deploy.max_parallel - 1])
            dispatch_items_queue = items[Deploy.max_parallel:]
        else:
            dispatch_items(items)

        all_done = False
        num_secs = 0
        status = {}
        status_str = {}
        status_str_prev = {}

        while not all_done:
            time.sleep(1)
            num_secs += 1
            trig_print = ((num_secs % Deploy.print_interval) == 0)
            for item in dispatched_items:
                if item.target not in status.keys():
                    status[item.target] = {}
                if item not in status[item.target].keys():
                    status[item.target][item] = ""

                if item.status == ".": item.get_status()
                if item.status != status[
                        item.target][item] and item.status != ".":
                    trig_print = True
                    if item.status != "P":
                        # Kill sub items
                        item.set_sub_status("K")
                    dispatch_items_queue.extend(item.sub)
                status[item.target][item] = item.status

            # Dispatch more from the queue
            if len(dispatch_items_queue) == 0:
                all_done = True
            else:
                num_slots = Deploy.max_parallel - Deploy.dispatch_counter
                if num_slots > 0:
                    if len(dispatch_items_queue) > num_slots:
                        dispatch_items(dispatch_items_queue[0:num_slots])
                        dispatch_items_queue = dispatch_items_queue[num_slots:]
                    else:
                        dispatch_items(dispatch_items_queue)
                        dispatch_items_queue = []

            status_str_prev = status_str.copy()
            status_str = {}
            for target in status.keys():
                if target not in status_str.keys(): status_str[target] = "["
                for item in status[target].keys():
                    if status[target][item] is not None:
                        status_str[target] += status[target][item]
                        if status[target][item] == ".":
                            all_done = False
                status_str[target] += "]"

            # Print the status string periodically
            if trig_print:
                for target in status_str.keys():
                    if (target in status_str_prev.keys()) and \
                       (status_str[target] == status_str_prev[target]) and \
                       (status_str[target].find(".") == -1):
                        continue
                    log.info("[dvsim]: [%06ds] [%s]: %s", num_secs, target,
                             status_str[target])


class CompileSim(Deploy):
    """
    Abstraction for building the simulation executable.
    """

    # Register all builds with the class
    items = []

    def __init__(self, build_mode, sim_cfg):
        self.target = "build"
        self.pass_patterns = []
        self.fail_patterns = []

        self.mandatory_cmd_attrs = {
            # tool srcs
            "simulator_srcs": False,
            "simulator_srcs_dir": False,

            # RAL gen
            "skip_ral": False,
            "gen_ral_pkg_cmd": False,
            "gen_ral_pkg_dir": False,
            "gen_ral_pkg_opts": False,

            # Flist gen
            "sv_flist_gen_cmd": False,
            "sv_flist_gen_dir": False,
            "sv_flist_gen_opts": False,

            # Build
            "build_dir": False,
            "build_cmd": False,
            "build_opts": False
        }

        self.mandatory_misc_attrs = {"cov_db_dir": False}

        # Initialize
        super().__init__(sim_cfg)
        super().parse_dict(build_mode.__dict__)
        # Call this method again with the sim_cfg dict passed as the object,
        # since it may contain additional mandatory attrs.
        super().parse_dict(sim_cfg.__dict__)
        self.build_mode = self.name
        self.__post_init__()

        # Start fail message construction
        self.fail_msg = "\n**BUILD:** {}<br>\n".format(self.name)
        log_sub_path = self.log.replace(self.sim_cfg.scratch_path + '/', '')
        self.fail_msg += "**LOG:** $scratch_path/{}<br>\n".format(log_sub_path)

        CompileSim.items.append(self)

    def dispatch_cmd(self):
        # Delete previous cov_db_dir if it exists before dispatching new build.
        if os.path.exists(self.cov_db_dir):
            os.system("rm -rf " + self.cov_db_dir)
        super().dispatch_cmd()


class RunTest(Deploy):
    """
    Abstraction for running tests. This is one per seed for each test.
    """

    # Initial seed values when running tests (if available).
    seeds = []

    # Register all runs with the class
    items = []

    def __init__(self, index, test, sim_cfg):
        self.target = "run"
        self.pass_patterns = []
        self.fail_patterns = []

        self.mandatory_cmd_attrs = {
            "uvm_test": False,
            "uvm_test_seq": False,
            "run_opts": False,
            "sw_dir": False,
            "sw_name": False,
            "run_dir": False,
            "run_cmd": False,
            "run_opts": False
        }

        self.mandatory_misc_attrs = {
            "run_dir_name": False,
            "cov_db_test_dir": False,
            "pass_patterns": False,
            "fail_patterns": False
        }

        self.index = index
        self.seed = RunTest.get_seed()

        # Initialize
        super().__init__(sim_cfg)
        super().parse_dict(test.__dict__)
        # Call this method again with the sim_cfg dict passed as the object,
        # since it may contain additional mandatory attrs.
        super().parse_dict(sim_cfg.__dict__)
        self.test = self.name
        self.renew_odir = True
        self.build_mode = test.build_mode.name
        self.__post_init__()
        # For output dir link, use run_dir_name instead.
        self.odir_ln = self.run_dir_name

        # Start fail message construction
        self.fail_msg = "\n**TEST:** {}, ".format(self.name)
        self.fail_msg += "**SEED:** {}<br>\n".format(self.seed)
        log_sub_path = self.log.replace(self.sim_cfg.scratch_root + '/', '')
        self.fail_msg += "**LOG:** {}<br>\n".format(log_sub_path)

        RunTest.items.append(self)

    def get_status(self):
        '''Override base class get_status implementation for additional post-status
        actions.'''
        super().get_status()
        if self.status not in [".", "P"]:
            # Delete the coverage data if available.
            if os.path.exists(self.cov_db_test_dir):
                log.log(VERBOSE, "Deleting coverage data of failing test:\n%s",
                        self.cov_db_test_dir)
                os.system("/usr/bin/rm -rf " + self.cov_db_test_dir)

    @staticmethod
    def get_seed():
        if not RunTest.seeds:
            for i in range(1000):
                seed = random.getrandbits(32)
                RunTest.seeds.append(seed)
        return RunTest.seeds.pop(0)


class CovMerge(Deploy):
    """
    Abstraction for merging coverage databases. An item of this class is created AFTER
    the regression is completed.
    """

    # Register all builds with the class
    items = []

    def __init__(self, sim_cfg):
        self.target = "cov_merge"
        self.pass_patterns = []
        self.fail_patterns = []

        # Construct local 'special' variable from cov directories that need to
        # be merged.
        self.cov_db_dirs = ""

        self.mandatory_cmd_attrs = {
            "cov_merge_cmd": False,
            "cov_merge_opts": False
        }

        self.mandatory_misc_attrs = {
            "cov_merge_dir": False,
            "cov_merge_db_dir": False
        }

        # Initialize
        super().__init__(sim_cfg)
        super().parse_dict(sim_cfg.__dict__)
        self.__post_init__()

        # Override standard output and log patterns.
        self.odir = self.cov_merge_db_dir
        self.odir_ln = os.path.basename(os.path.normpath(self.odir))

        # Start fail message construction
        self.fail_msg = "\n**COV_MERGE:** {}<br>\n".format(self.name)
        log_sub_path = self.log.replace(self.sim_cfg.scratch_path + '/', '')
        self.fail_msg += "**LOG:** $scratch_path/{}<br>\n".format(log_sub_path)

        CovMerge.items.append(self)

    def __post_init__(self):
        # Add cov db dirs from all the builds that were kicked off.
        for bld in self.sim_cfg.builds:
            self.cov_db_dirs += bld.cov_db_dir + " "

        # Recursively search and replace wildcards, ignoring cov_db_dirs for now.
        # We need to resolve it later based on cov_db_dirs value set below.
        self.__dict__ = find_and_substitute_wildcards(
            self.__dict__, self.__dict__, ignored_wildcards=["cov_db_dirs"])

        # Prune previous merged cov directories.
        prev_cov_db_dirs = self.odir_limiter(odir=self.cov_merge_db_dir)

        # If a merged cov data base exists from a previous run, then consider
        # that as well for merging, if the --cov-merge-previous command line
        # switch is passed.
        if self.sim_cfg.cov_merge_previous:
            self.cov_db_dirs += prev_cov_db_dirs

        # Call base class __post_init__ to do checks and substitutions
        super().__post_init__()


class CovReport(Deploy):
    """
    Abstraction for coverage report generation. An item of this class is created AFTER
    the regression is completed.
    """

    # Register all builds with the class
    items = []

    def __init__(self, sim_cfg):
        self.target = "cov_report"
        self.pass_patterns = []
        self.fail_patterns = []
        self.cov_results = ""

        self.mandatory_cmd_attrs = {
            "cov_report_cmd": False,
            "cov_report_opts": False
        }

        self.mandatory_misc_attrs = {
            "cov_report_dir": False,
            "cov_merge_db_dir": False,
            "cov_report_dashboard": False
        }

        # Initialize
        super().__init__(sim_cfg)
        super().parse_dict(sim_cfg.__dict__)
        self.__post_init__()

        # Start fail message construction
        self.fail_msg = "\n**COV_REPORT:** {}<br>\n".format(self.name)
        log_sub_path = self.log.replace(self.sim_cfg.scratch_path + '/', '')
        self.fail_msg += "**LOG:** $scratch_path/{}<br>\n".format(log_sub_path)

        CovReport.items.append(self)

    def get_status(self):
        super().get_status()
        # Once passed, extract the cov results summary from the dashboard.
        if self.status == "P":
            try:
                with open(self.cov_report_dashboard, 'r') as f:
                    for line in f:
                        match = re.match("total coverage summary", line,
                                         re.IGNORECASE)
                        if match:
                            results = []
                            # Metrics on the next line.
                            line = f.readline().strip()
                            results.append(line.split())
                            # Values on the next.
                            line = f.readline().strip()
                            # Pretty up the values - add % sign for ease of post
                            # processing.
                            values = []
                            for val in line.split():
                                val += " %"
                                values.append(val)
                            results.append(values)
                            colalign = (("center", ) * len(values))
                            self.cov_results = tabulate(results,
                                                        headers="firstrow",
                                                        tablefmt="pipe",
                                                        colalign=colalign)
                            break

            except Exception as e:
                ex_msg = "Failed to parse \"{}\":\n{}".format(
                    self.cov_report_dashboard, str(e))
                log.fail_msg += ex_msg
                log.error(ex_msg)
                self.status = "F"

            if self.cov_results == "":
                nf_msg = "Coverage summary not found in the reports dashboard!"
                log.fail_msg += nf_msg
                log.error(nf_msg)
                self.status = "F"

        if self.status == "P":
            # Delete the cov report - not needed.
            os.system("rm -rf " + self.log)


class CovAnalyze(Deploy):
    """
    Abstraction for coverage analysis tool.
    """

    # Register all builds with the class
    items = []

    def __init__(self, sim_cfg):
        self.target = "cov_analyze"
        self.pass_patterns = []
        self.fail_patterns = []

        self.mandatory_cmd_attrs = {
            "cov_analyze_cmd": False,
            "cov_analyze_opts": False
        }

        self.mandatory_misc_attrs = {
            "cov_analyze_dir": False,
            "cov_merge_db_dir": False
        }

        # Initialize
        super().__init__(sim_cfg)
        super().parse_dict(sim_cfg.__dict__)
        self.__post_init__()

        # Start fail message construction
        self.fail_msg = "\n**COV_ANALYZE:** {}<br>\n".format(self.name)
        log_sub_path = self.log.replace(self.sim_cfg.scratch_path + '/', '')
        self.fail_msg += "**LOG:** $scratch_path/{}<br>\n".format(log_sub_path)

        CovAnalyze.items.append(self)
