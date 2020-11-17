# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import logging as log
import os
import pprint
import random
import re
import shlex
import subprocess
import sys
import time
from collections import OrderedDict

from sim_utils import get_cov_summary_table
from tabulate import tabulate
from utils import VERBOSE, find_and_substitute_wildcards, run_cmd


class Deploy():
    """
    Abstraction for deploying builds and runs.
    """

    # Timer in hours, minutes and seconds.
    hh = 0
    mm = 0
    ss = 0

    # Maintain a list of dispatched items.
    dispatch_counter = 0

    # Misc common deploy settings.
    print_legend = True
    print_interval = 5
    max_parallel = 16
    max_odirs = 5
    # Max jobs dispatched in one go.
    slot_limit = 20

    def __self_str__(self):
        if log.getLogger().isEnabledFor(VERBOSE):
            return pprint.pformat(self.__dict__)
        else:
            ret = self.cmd
            if self.sub != []:
                ret += "\nSub:\n" + str(self.sub)
            return ret

    def __str__(self):
        return self.__self_str__()

    def __repr__(self):
        return self.__self_str__()

    def __init__(self, sim_cfg):
        '''Initialize common class members.'''

        # Cross ref the whole cfg object for ease.
        self.sim_cfg = sim_cfg

        # Common vars
        self.identifier = ""
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
        self.exports = None

        # Deploy sub commands
        self.sub = []

        # Process
        self.process = None
        self.log_fd = None
        self.status = None

        # These are mandatory class attributes that need to be extracted and
        # set from the sim_cfg object. These are explicitly used to construct
        # the command for deployment.
        self.mandatory_cmd_attrs = {}

        # These are mandatory class attributes that also need to be extracted
        # and set from the sim_cfg object. Some of these contribute to the
        # construction of the command. Others are used to determine pass / fail
        # conditions.
        self.mandatory_misc_attrs = {
            "name": False,
            "build_mode": False,
            "flow_makefile": False,
            "exports": False,
            "dry_run": False
        }

    # Function to parse a dict and extract the mandatory cmd and misc attrs.
    def parse_dict(self, ddict):
        if not hasattr(self, "target"):
            log.error(
                "Class %s does not have the mandatory attribute \"target\" defined",
                self.__class__.__name__)
            sys.exit(1)

        ddict_keys = ddict.keys()
        for key in self.mandatory_cmd_attrs.keys():
            if self.mandatory_cmd_attrs[key] is False:
                if key in ddict_keys:
                    setattr(self, key, ddict[key])
                    self.mandatory_cmd_attrs[key] = True

        for key in self.mandatory_misc_attrs.keys():
            if self.mandatory_misc_attrs[key] is False:
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
        # First pass: search within self dict. We ignore errors since some
        # substitions may be available in the second pass.
        self.__dict__ = find_and_substitute_wildcards(self.__dict__,
                                                      self.__dict__, [], True)

        # Second pass: search in sim_cfg dict, this time not ignoring errors.
        self.__dict__ = find_and_substitute_wildcards(self.__dict__,
                                                      self.sim_cfg.__dict__,
                                                      [], False)

        # Set identifier.
        self.identifier = self.sim_cfg.name + ":" + self.name

        # Set the command, output dir and log
        self.odir = getattr(self, self.target + "_dir")
        # Set the output dir link name to the basename of odir (by default)
        self.odir_ln = os.path.basename(os.path.normpath(self.odir))
        self.log = self.odir + "/" + self.target + ".log"

        # Make exports more easily mergeable with the current process' env.
        self._process_exports()

        # If using LSF, redirect stdout and err to the log file
        self.cmd = self.construct_cmd()

    def _process_exports(self):
        '''Convert 'exports' as a list of dicts in the HJson to a dict.

        Exports is a list of key-value pairs that are to be exported to the
        subprocess' environment so that the tools can lookup those options.
        DVSim limits how the data is presented in the HJson (the value of a
        HJson member cannot be an object). This method converts a list of dicts
        into a dict variable, which makes it easy to merge the list of exports
        with the subprocess' env where the ASIC tool is invoked.
        '''
        exports_dict = {}
        if self.exports:
            try:
                exports_dict = {
                    k: str(v)
                    for item in self.exports for k, v in item.items()
                }
            except ValueError as e:
                log.error(
                    "%s: exports: \'%s\' Exports key must be a list of dicts!",
                    e, str(self.exports))
                sys.exit(1)
        self.exports = exports_dict

    def construct_cmd(self):
        cmd = "make -f " + self.flow_makefile + " " + self.target
        if self.dry_run is True:
            cmd += " -n"
        for attr in sorted(self.mandatory_cmd_attrs.keys()):
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

    def is_equivalent_job(self, item):
        '''Checks if job that would be dispatched with `item` is equivalent to
        `self`.

        Determines if `item` and `self` would behave exactly the same way when
        deployed. If so, then there is no point in keeping both. The caller can
        choose to discard `item` and pick `self` instead. To do so, we check
        the final resolved `cmd` & the exports. The `name` field will be unique
        to `item` and `self`, so we take that out of the comparison.
        '''
        if type(self) != type(item):
            return False

        # Check if the cmd field is identical.
        item_cmd = item.cmd.replace(item.name, self.name)
        if self.cmd != item_cmd:
            return False

        # Check if exports have identical set of keys.
        if self.exports.keys() != item.exports.keys():
            return False

        # Check if exports have identical values.
        for key, val in self.exports.items():
            item_val = item.exports[key]
            if type(item_val) is str:
                item_val = item_val.replace(item.name, self.name)
            if val != item_val:
                return False

        log.log(VERBOSE, "Deploy job \"%s\" is equivalent to \"%s\"",
                item.name, self.name)
        return True

    def dispatch_cmd(self):
        # Update the shell's env vars with self.exports. Values in exports must
        # replace the values in the shell's env vars if the keys match.
        exports = os.environ.copy()
        exports.update(self.exports)

        args = shlex.split(self.cmd)
        try:
            # If renew_odir flag is True - then move it.
            if self.renew_odir:
                self.odir_limiter(odir=self.odir)
            os.system("mkdir -p " + self.odir)
            # Dump all env variables for ease of debug.
            with open(self.odir + "/env_vars",
                      "w",
                      encoding="UTF-8",
                      errors="surrogateescape") as f:
                for var in sorted(exports.keys()):
                    f.write("{}={}\n".format(var, exports[var]))
                f.close()
            os.system("ln -s " + self.odir + " " + self.sim_cfg.links['D'] +
                      '/' + self.odir_ln)
            f = open(self.log, "w", encoding="UTF-8", errors="surrogateescape")
            f.write("[Executing]:\n{}\n\n".format(self.cmd))
            f.flush()
            self.process = subprocess.Popen(args,
                                            bufsize=4096,
                                            universal_newlines=True,
                                            stdout=f,
                                            stderr=f,
                                            env=exports)
            self.log_fd = f
            self.status = "D"
            Deploy.dispatch_counter += 1
        except IOError:
            log.error('IO Error: See %s', self.log)
            if self.log_fd:
                self.log_fd.close()
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
                if max_odirs == -1:
                    max_odirs = self.max_odirs
                num_rm_dirs = num_dirs - max_odirs
                if num_rm_dirs > -1:
                    rm_dirs = run_cmd(find_cmd +
                                      "-printf '%T+ %p\n' | sort | head -n " +
                                      str(num_rm_dirs + 1) +
                                      " | awk '{print $2}'")
                    rm_dirs = rm_dirs.replace('\n', ' ')
                    dirs = dirs.replace(rm_dirs, "")
                    os.system("/bin/rm -rf " + rm_dirs)
        except IOError:
            log.error("Failed to delete old run directories!")
        return dirs

    def set_status(self):
        self.status = 'P'
        if self.dry_run is False:
            seen_fail_pattern = False
            for fail_pattern in self.fail_patterns:
                # Return error message with the following 4 lines.
                grep_cmd = "grep -m 1 -A 4 -E \'" + fail_pattern + "\' " + self.log
                (status, rslt) = subprocess.getstatusoutput(grep_cmd)
                if rslt:
                    msg = "```\n{}\n```\n".format(rslt)
                    self.fail_msg += msg
                    log.log(VERBOSE, msg)
                    self.status = 'F'
                    seen_fail_pattern = True
                    break

            # If fail patterns were not encountered, but the job returned with non-zero exit code
            # for whatever reason, then show the last 10 lines of the log as the failure message,
            # which might help with the debug.
            if self.process.returncode != 0 and not seen_fail_pattern:
                msg = "Last 10 lines of the log:<br>\n"
                self.fail_msg += msg
                log.log(VERBOSE, msg)
                get_fail_msg_cmd = "tail -n 10 " + self.log
                msg = run_cmd(get_fail_msg_cmd)
                msg = "```\n{}\n```\n".format(msg)
                self.fail_msg += msg
                log.log(VERBOSE, msg)
                self.status = "F"

            # Return if status is fail - no need to look for pass patterns.
            if self.status == 'F':
                return

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
            if os.system(cmd):
                log.error("Cmd \"%s\" could not be run", cmd)

    def get_status(self):
        if self.status != "D":
            return
        if self.process.poll() is not None:
            self.log_fd.close()
            self.set_status()

            log.debug("Item %s has completed execution: %s", self.name,
                      self.status)
            Deploy.dispatch_counter -= 1
            self.link_odir()
            del self.process

    def kill(self):
        '''Kill running processes.
        '''
        if self.status == "D" and self.process.poll() is None:
            self.kill_remote_job()

            # Try to kill the running process. Send SIGTERM first, wait a bit,
            # and then send SIGKILL if it didn't work.
            self.process.terminate()
            try:
                self.process.wait(timeout=2)
            except subprocess.TimeoutExpired:
                self.process.kill()

            if self.log_fd:
                self.log_fd.close()
            self.status = "K"
        # recurisvely kill sub target
        elif len(self.sub):
            for item in self.sub:
                item.kill()

    def kill_remote_job(self):
        '''
        If jobs are run in remote server, need to use another command to kill them.
        '''
        # TODO: Currently only support lsf, may need to add support for GCP later.

        # If use lsf, kill it by job ID.
        if re.match("^bsub", self.sim_cfg.job_prefix):
            # get job id from below string
            # Job <xxxxxx> is submitted to default queue
            grep_cmd = "grep -m 1 -E \'" + "^Job <" + "\' " + self.log
            (status, rslt) = subprocess.getstatusoutput(grep_cmd)
            if rslt != "":
                job_id = rslt.split('Job <')[1].split('>')[0]
                try:
                    subprocess.run(["bkill", job_id], check=True)
                except Exception as e:
                    log.error("%s: Failed to run bkill\n", e)

    @staticmethod
    def increment_timer():
        # sub function that increments with overflow = 60
        def _incr_ovf_60(val):
            if val >= 59:
                val = 0
                return val, True
            else:
                val += 1
                return val, False

        incr_hh = False
        Deploy.ss, incr_mm = _incr_ovf_60(Deploy.ss)
        if incr_mm:
            Deploy.mm, incr_hh = _incr_ovf_60(Deploy.mm)
        if incr_hh:
            Deploy.hh += 1

    @staticmethod
    def deploy(items):
        dispatched_items = []
        queued_items = []

        # Print timer val in hh:mm:ss.
        def get_timer_val():
            return "%02i:%02i:%02i" % (Deploy.hh, Deploy.mm, Deploy.ss)

        # Check if elapsed time has reached the next print interval.
        def has_print_interval_reached():
            # Deploy.print_interval is expected to be < 1 hour.
            return (((Deploy.mm * 60 + Deploy.ss) %
                     Deploy.print_interval) == 0)

        def dispatch_items(items):
            item_names = OrderedDict()
            for item in items:
                if item.target not in item_names.keys():
                    item_names[item.target] = ""
                if item.status is None:
                    item_names[item.target] += item.identifier + ", "
                    item.dispatch_cmd()

            for target in item_names.keys():
                if item_names[target] != "":
                    item_names[target] = "  [" + item_names[target][:-2] + "]"
                    log.log(VERBOSE, "[%s]: [%s]: [dispatch]:\n%s",
                            get_timer_val(), target, item_names[target])

        # Initialize status for a target, add '_stats_' for the said target
        # and initialize counters for queued, dispatched, passed, failed,
        # killed and total to 0. Also adds a boolean key to indicate if all
        # items in a given target are done.
        def init_status_target_stats(status, target):
            status[target] = OrderedDict()
            status[target]['_stats_'] = OrderedDict()
            status[target]['_stats_']['Q'] = 0
            status[target]['_stats_']['D'] = 0
            status[target]['_stats_']['P'] = 0
            status[target]['_stats_']['F'] = 0
            status[target]['_stats_']['K'] = 0
            status[target]['_stats_']['T'] = 0
            status[target]['_done_'] = False

        # Update status counter for a newly queued item.
        def add_status_target_queued(status, item):
            if item.target not in status.keys():
                init_status_target_stats(status, item.target)
            status[item.target][item] = "Q"
            status[item.target]['_stats_']['Q'] += 1
            status[item.target]['_stats_']['T'] += 1

        # Update status counters for a target.
        def update_status_target_stats(status, item):
            old_status = status[item.target][item]
            status[item.target]['_stats_'][old_status] -= 1
            status[item.target]['_stats_'][item.status] += 1
            status[item.target][item] = item.status

        def check_if_done_and_print_status(status, print_status_flag):
            all_done = True
            for target in status.keys():
                target_done_prev = status[target]['_done_']
                target_done_curr = ((status[target]['_stats_']["Q"] == 0) and
                                    (status[target]['_stats_']["D"] == 0))
                status[target]['_done_'] = target_done_curr
                all_done &= target_done_curr

                # Print if flag is set and target_done is not True for two
                # consecutive times.
                if not (target_done_prev and
                        target_done_curr) and print_status_flag:
                    stats = status[target]['_stats_']
                    width = "0{}d".format(len(str(stats["T"])))
                    msg = "["
                    for s in stats.keys():
                        msg += s + ": {:{}}, ".format(stats[s], width)
                    msg = msg[:-2] + "]"
                    log.info("[%s]: [%s]: %s", get_timer_val(), target, msg)
            return all_done

        # Print legend once at the start of the run.
        if Deploy.print_legend:
            log.info("[legend]: [Q: queued, D: dispatched, "
                     "P: passed, F: failed, K: killed, T: total]")
            Deploy.print_legend = False

        status = OrderedDict()
        print_status_flag = True

        # Queue all items
        queued_items = items
        for item in queued_items:
            add_status_target_queued(status, item)

        all_done = False
        while not all_done:
            # Get status of dispatched items.
            for item in dispatched_items:
                if item.status == "D":
                    item.get_status()
                if item.status != status[item.target][item]:
                    print_status_flag = True
                    if item.status != "D":
                        if item.status != "P":
                            # Kill its sub items if item did not pass.
                            item.set_sub_status("K")
                            log.error("[%s]: [%s]: [status] [%s: %s]",
                                      get_timer_val(), item.target,
                                      item.identifier, item.status)
                        else:
                            log.log(VERBOSE, "[%s]: [%s]: [status] [%s: %s]",
                                    get_timer_val(), item.target,
                                    item.identifier, item.status)
                        # Queue items' sub-items if it is done.
                        queued_items.extend(item.sub)
                        for sub_item in item.sub:
                            add_status_target_queued(status, sub_item)
                    update_status_target_stats(status, item)

            # Dispatch items from the queue as slots free up.
            all_done = (len(queued_items) == 0)
            if not all_done:
                num_slots = Deploy.max_parallel - Deploy.dispatch_counter
                if num_slots > Deploy.slot_limit:
                    num_slots = Deploy.slot_limit
                if num_slots > 0:
                    if len(queued_items) > num_slots:
                        dispatch_items(queued_items[0:num_slots])
                        dispatched_items.extend(queued_items[0:num_slots])
                        queued_items = queued_items[num_slots:]
                    else:
                        dispatch_items(queued_items)
                        dispatched_items.extend(queued_items)
                        queued_items = []

            # Check if we are done and print the status periodically.
            all_done &= check_if_done_and_print_status(status,
                                                       print_status_flag)

            # Advance time by 1s if there is more work to do.
            if not all_done:
                time.sleep(1)
                Deploy.increment_timer()
                print_status_flag = has_print_interval_reached()


class CompileSim(Deploy):
    """
    Abstraction for building the simulation executable.
    """

    # Register all builds with the class
    items = []

    def __init__(self, build_mode, sim_cfg):
        # Initialize common vars.
        super().__init__(sim_cfg)

        self.target = "build"
        self.pass_patterns = []
        self.fail_patterns = []

        self.mandatory_cmd_attrs.update({
            # tool srcs
            "tool_srcs": False,
            "tool_srcs_dir": False,

            # Flist gen
            "sv_flist_gen_cmd": False,
            "sv_flist_gen_dir": False,
            "sv_flist_gen_opts": False,

            # Build
            "build_dir": False,
            "build_cmd": False,
            "build_opts": False
        })

        self.mandatory_misc_attrs.update({
            "cov_db_dir": False,
            "build_pass_patterns": False,
            "build_fail_patterns": False
        })

        super().parse_dict(build_mode.__dict__)
        # Call this method again with the sim_cfg dict passed as the object,
        # since it may contain additional mandatory attrs.
        super().parse_dict(sim_cfg.__dict__)
        self.build_mode = self.name
        self.pass_patterns = self.build_pass_patterns
        self.fail_patterns = self.build_fail_patterns
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


class CompileOneShot(Deploy):
    """
    Abstraction for building the simulation executable.
    """

    # Register all builds with the class
    items = []

    def __init__(self, build_mode, sim_cfg):
        # Initialize common vars.
        super().__init__(sim_cfg)

        self.target = "build"
        self.pass_patterns = []
        self.fail_patterns = []

        self.mandatory_cmd_attrs.update({
            # tool srcs
            "tool_srcs": False,
            "tool_srcs_dir": False,

            # Flist gen
            "sv_flist_gen_cmd": False,
            "sv_flist_gen_dir": False,
            "sv_flist_gen_opts": False,

            # Build
            "build_dir": False,
            "build_cmd": False,
            "build_opts": False,
            "build_log": False,

            # Report processing
            "report_cmd": False,
            "report_opts": False
        })

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

        CompileOneShot.items.append(self)


class RunTest(Deploy):
    """
    Abstraction for running tests. This is one per seed for each test.
    """

    # Initial seed values when running tests (if available).
    seeds = []
    fixed_seed = None

    # Register all runs with the class
    items = []

    def __init__(self, index, test, sim_cfg):
        # Initialize common vars.
        super().__init__(sim_cfg)

        self.target = "run"
        self.pass_patterns = []
        self.fail_patterns = []

        self.mandatory_cmd_attrs.update({
            # tool srcs
            "tool_srcs": False,
            "tool_srcs_dir": False,

            "proj_root": False,
            "uvm_test": False,
            "uvm_test_seq": False,
            "run_opts": False,
            "sw_test": False,
            "sw_test_is_prebuilt": False,
            "sw_build_device": False,
            "sw_build_dir": False,
            "run_dir": False,
            "run_cmd": False,
            "run_opts": False
        })

        self.mandatory_misc_attrs.update({
            "run_dir_name": False,
            "cov_db_test_dir": False,
            "run_pass_patterns": False,
            "run_fail_patterns": False
        })

        self.index = index
        self.seed = RunTest.get_seed()

        super().parse_dict(test.__dict__)
        # Call this method again with the sim_cfg dict passed as the object,
        # since it may contain additional mandatory attrs.
        super().parse_dict(sim_cfg.__dict__)
        self.test = self.name
        self.renew_odir = True
        self.build_mode = test.build_mode.name
        self.pass_patterns = self.run_pass_patterns
        self.fail_patterns = self.run_fail_patterns
        self.__post_init__()
        # For output dir link, use run_dir_name instead.
        self.odir_ln = self.run_dir_name

        # Start fail message construction
        self.fail_msg = "\n**TEST:** {}, ".format(self.name)
        self.fail_msg += "**SEED:** {}<br>\n".format(self.seed)
        log_sub_path = self.log.replace(self.sim_cfg.scratch_path + '/', '')
        self.fail_msg += "**LOG:** $scratch_path/{}<br>\n".format(log_sub_path)

        RunTest.items.append(self)

    def __post_init__(self):
        super().__post_init__()
        # Set identifier.
        self.identifier = self.sim_cfg.name + ":" + self.run_dir_name

    def get_status(self):
        '''Override base class get_status implementation for additional post-status
        actions.'''
        super().get_status()
        if self.status not in ["D", "P"]:
            # Delete the coverage data if available.
            if os.path.exists(self.cov_db_test_dir):
                log.log(VERBOSE, "Deleting coverage data of failing test:\n%s",
                        self.cov_db_test_dir)
                os.system("/bin/rm -rf " + self.cov_db_test_dir)

    @staticmethod
    def get_seed():
        # If --seeds option is passed, then those custom seeds are consumed
        # first. If --fixed-seed <val> is also passed, the subsequent tests
        # (once the custom seeds are consumed) will be run with the fixed seed.
        if not RunTest.seeds:
            if RunTest.fixed_seed:
                return RunTest.fixed_seed
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
        # Initialize common vars.
        super().__init__(sim_cfg)

        self.target = "cov_merge"
        self.pass_patterns = []
        self.fail_patterns = []

        # Construct local 'special' variable from cov directories that need to
        # be merged.
        self.cov_db_dirs = ""

        self.mandatory_cmd_attrs.update({
            "cov_merge_cmd": False,
            "cov_merge_opts": False
        })

        self.mandatory_misc_attrs.update({
            "cov_merge_dir": False,
            "cov_merge_db_dir": False
        })

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

        # Recursively search and replace wildcards, ignoring cov_db_dirs.
        # We need to resolve it later based on cov_db_dirs value set below.

        # First pass: search within self dict. We ignore errors since some
        # substitions may be available in the second pass.
        self.__dict__ = find_and_substitute_wildcards(
            self.__dict__,
            self.__dict__,
            ignored_wildcards=["cov_db_dirs"],
            ignore_error=True)

        # Second pass: search in sim_cfg dict, this time not ignoring errors.
        self.__dict__ = find_and_substitute_wildcards(
            self.__dict__,
            self.sim_cfg.__dict__,
            ignored_wildcards=["cov_db_dirs"],
            ignore_error=False)

        # Call base class __post_init__ to do checks and substitutions
        super().__post_init__()

        # Prune previous merged cov directories.
        prev_cov_db_dirs = self.odir_limiter(odir=self.cov_merge_db_dir)

        # If a merged cov data base exists from a previous run, then consider
        # that as well for merging, if the --cov-merge-previous command line
        # switch is passed.
        if self.sim_cfg.cov_merge_previous:
            self.cov_db_dirs += prev_cov_db_dirs

        # Append cov_db_dirs to the list of exports.
        self.exports["cov_db_dirs"] = "\"{}\"".format(self.cov_db_dirs)


class CovReport(Deploy):
    """
    Abstraction for coverage report generation. An item of this class is created AFTER
    the regression is completed.
    """

    # Register all builds with the class
    items = []

    def __init__(self, sim_cfg):
        # Initialize common vars.
        super().__init__(sim_cfg)

        self.target = "cov_report"
        self.pass_patterns = []
        self.fail_patterns = []
        self.cov_total = ""
        self.cov_results = ""

        self.mandatory_cmd_attrs.update({
            "cov_report_cmd": False,
            "cov_report_opts": False
        })

        self.mandatory_misc_attrs.update({
            "cov_report_dir": False,
            "cov_merge_db_dir": False,
            "cov_report_txt": False
        })

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
            results, self.cov_total, ex_msg = get_cov_summary_table(
                self.cov_report_txt, self.sim_cfg.tool)

            if not ex_msg:
                # Succeeded in obtaining the coverage data.
                colalign = (("center", ) * len(results[0]))
                self.cov_results = tabulate(results,
                                            headers="firstrow",
                                            tablefmt="pipe",
                                            colalign=colalign)
            else:
                self.fail_msg += ex_msg
                log.error(ex_msg)
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
        # Initialize common vars.
        super().__init__(sim_cfg)

        self.target = "cov_analyze"
        self.pass_patterns = []
        self.fail_patterns = []

        self.mandatory_cmd_attrs.update({
            # tool srcs
            "tool_srcs": False,
            "tool_srcs_dir": False,
            "cov_analyze_cmd": False,
            "cov_analyze_opts": False
        })

        self.mandatory_misc_attrs.update({
            "cov_analyze_dir": False,
            "cov_merge_db_dir": False
        })

        super().parse_dict(sim_cfg.__dict__)
        self.__post_init__()

        # Start fail message construction
        self.fail_msg = "\n**COV_ANALYZE:** {}<br>\n".format(self.name)
        log_sub_path = self.log.replace(self.sim_cfg.scratch_path + '/', '')
        self.fail_msg += "**LOG:** $scratch_path/{}<br>\n".format(log_sub_path)

        CovAnalyze.items.append(self)
