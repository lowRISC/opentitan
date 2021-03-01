# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import logging as log
import os
import pprint
import random
import re
import shlex
import shutil
import subprocess
import sys
from datetime import datetime
from pathlib import Path

from sim_utils import get_cov_summary_table
from tabulate import tabulate
from utils import TS_FORMAT, VERBOSE, find_and_substitute_wildcards, rm_path


class DeployError(Exception):
    def __init__(self, msg):
        self.msg = msg


class Deploy():
    """
    Abstraction for deploying builds and runs.
    """

    # Misc common deploy settings.
    max_odirs = 5

    # List of variable names that are to be treated as "list of commands".
    # This tells `construct_cmd` that these vars are lists that need to
    # be joined with '&&' instead of a space.
    cmds_list_vars = []

    def __str__(self):
        return (pprint.pformat(self.__dict__)
                if log.getLogger().isEnabledFor(VERBOSE) else self.cmd)

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

        # A list of jobs on which this job depends
        self.dependencies = []

        # Indicates whether running this job requires all dependencies to pass.
        # If this flag is set to False, any passing dependency will trigger
        # this current job to run
        self.needs_all_dependencies_passing = True

        # Process
        self.process = None
        self.log_fd = None

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
                # Join attributes that are list of commands with '&&' to chain
                # them together when executed as a Make target's recipe.
                separator = " && " if attr in self.cmds_list_vars else " "
                value = separator.join(pretty_value)
            if type(value) is bool:
                value = int(value)
            if type(value) is str:
                value = value.strip()
            cmd += " " + attr + "=\"" + str(value) + "\""
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

        # Clear the magic MAKEFLAGS variable from exports if necessary. This
        # variable is used by recursive Make calls to pass variables from one
        # level to the next. Here, self.cmd is a call to Make but it's
        # logically a top-level invocation: we don't want to pollute the flow's
        # Makefile with Make variables from any wrapper that called dvsim.
        if 'MAKEFLAGS' in exports:
            del exports['MAKEFLAGS']

        args = shlex.split(self.cmd)
        try:
            # If renew_odir flag is True - then move it.
            if self.renew_odir:
                self.odir_limiter(odir=self.odir)
            os.makedirs(self.odir, exist_ok=True)
            # Dump all env variables for ease of debug.
            with open(self.odir + "/env_vars",
                      "w",
                      encoding="UTF-8",
                      errors="surrogateescape") as f:
                for var in sorted(exports.keys()):
                    f.write("{}={}\n".format(var, exports[var]))
                f.close()
            self._link_odir("D")
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
        except IOError:
            if self.log_fd:
                self.log_fd.close()
            raise DeployError('IO Error: See {}'.format(self.log))

    def odir_limiter(self, odir):
        """Clean previous output directories.

        When running jobs, we may want to maintain a limited history of
        previous invocations. This method finds and deletes the output
        directories at the base of input arg 'odir' with the oldest timestamps,
        if that limit is reached. It returns a list of directories that
        remain after deletion.
        """

        if os.path.exists(odir):
            # If output directory exists, back it up.
            ts = datetime.fromtimestamp(os.stat(odir).st_ctime)
            ts = ts.strftime(TS_FORMAT)
            shutil.move(odir, odir + "_" + ts)

        # Get list of past output directories sorted by creation time.
        pdir = Path(odir).resolve().parent
        if not pdir.exists():
            return []

        dirs = sorted([old for old in pdir.iterdir() if old.is_dir()],
                      key=os.path.getctime,
                      reverse=True)

        for old in dirs[self.max_odirs - 1:]:
            rm_path(old)

        return dirs[0:self.max_odirs - 2]

    def _test_passed(self):
        """Determine the outcome of the job (P/F if it ran to completion).

        Return True if the job passed, False otherwise. This is called by
        poll() just after the job finishes.

        """
        def log_fail_msg(msg):
            '''Logs the fail msg to the final report.'''
            self.fail_msg += msg
            log.log(VERBOSE, msg)

        def _find_patterns(patterns, line):
            '''Helper function that returns true if all or any of the given
            patterns is found, else False.'''

            assert patterns
            for pattern in patterns:
                match = re.search(r"{}".format(pattern), line)
                if match:
                    return pattern
            return None

        def _get_n_lines(pos, num):
            "Helper function that returns next N lines starting at pos index."

            return ''.join(lines[pos:pos + num - 1]).strip()

        if self.dry_run:
            return True

        # Only one fail pattern needs to be seen.
        failed = False
        chk_failed = bool(self.fail_patterns)

        # All pass patterns need to be seen, so we replicate the list and remove
        # patterns as we encounter them.
        pass_patterns = self.pass_patterns.copy()
        chk_passed = bool(pass_patterns) and (self.process.returncode == 0)

        try:
            with open(self.log, "r", encoding="UTF-8") as f:
                lines = f.readlines()
        except OSError as e:
            log_fail_msg("Error opening file {!r}:\n{}".format(self.log, e))
            return False

        if chk_failed or chk_passed:
            for cnt, line in enumerate(lines):
                if chk_failed:
                    if _find_patterns(self.fail_patterns, line) is not None:
                        # Print 4 additional lines to help debug more easily.
                        log_fail_msg("```\n{}\n```\n".format(
                            _get_n_lines(cnt, 5)))
                        failed = True
                        chk_failed = False
                        chk_passed = False

                if chk_passed:
                    pattern = _find_patterns(pass_patterns, line)
                    if pattern is not None:
                        pass_patterns.remove(pattern)
                        chk_passed = bool(pass_patterns)

        # If failed, then nothing else to do. Just return.
        if failed:
            return False

        # If no fail patterns were seen, but the job returned with non-zero
        # exit code for whatever reason, then show the last 10 lines of the log
        # as the failure message, which might help with the debug.
        if self.process.returncode != 0:
            msg = ''.join(lines[-10:]).strip()
            log_fail_msg("Process returned non-zero exit code. "
                         "Last 10 lines:\n```\n{}\n```\n".format(msg))
            return False

        # Ensure all pass patterns were seen.
        if chk_passed:
            msg = ''.join(lines[-10:]).strip()
            log_fail_msg("One or more pass patterns not found:\n{}\n"
                         "Last 10 lines:\n```\n{}\n```\n".format(
                             pass_patterns, msg))
            return False

        return True

    def _link_odir(self, status):
        '''Soft-links the job's directory based on job's status, into
        dispatched, running, passed, failed or killed directories in the
        scratch area.'''

        dest = Path(self.sim_cfg.links[status], self.odir_ln)

        # If dest exists, then atomically remove it and link the odir again.
        while True:
            try:
                os.symlink(self.odir, dest)
                break
            except FileExistsError:
                rm_path(dest)

        # Delete the symlink from dispatched directory if it exists.
        if status != "D":
            old = Path(self.sim_cfg.links['D'], self.odir_ln)
            rm_path(old)

    def _on_finish(self, status):
        '''Called when the process finishes or is killed'''
        assert status in ['P', 'F', 'K']
        if status in ['P', 'F']:
            self._link_odir(status)

    def poll(self):
        '''Check status of the running process

        This returns 'D', 'P' or 'F'. If 'D', the job is still running. If 'P',
        the job finished successfully. If 'F', the job finished with an error.

        This function must only be called after running self.dispatch_cmd() and
        must not be called again once it has returned 'P' or 'F'.

        '''
        assert self.process is not None
        if self.process.poll() is None:
            return 'D'
        self.log_fd.close()

        status = 'P' if self._test_passed() else 'F'

        log.debug("Item %s has completed execution: %s", self.name, status)
        self._on_finish(status)

        del self.process
        self.process = None

        return status

    def kill(self):
        '''Kill the running process.

        This must be called between dispatching and reaping the process (the
        same window as poll()).

        '''
        assert self.process is not None
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
        self.process = None
        self._on_finish('K')

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


class CompileSim(Deploy):
    """
    Abstraction for building the simulation executable.
    """

    # Register all builds with the class
    items = []

    cmds_list_vars = ["pre_build_cmds", "post_build_cmds"]

    def __init__(self, build_mode, sim_cfg):
        # Initialize common vars.
        super().__init__(sim_cfg)

        self.target = "build"
        self.pass_patterns = []
        self.fail_patterns = []

        self.mandatory_cmd_attrs.update({
            # tool srcs
            "proj_root": False,

            # Flist gen
            "sv_flist_gen_cmd": False,
            "sv_flist_gen_dir": False,
            "sv_flist_gen_opts": False,

            # Build
            "build_dir": False,
            "pre_build_cmds": False,
            "build_cmd": False,
            "build_opts": False,
            "post_build_cmds": False,
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
        # Delete old coverage database directories before building again. We
        # need to do this becuase build directory is not 'renewed'.
        rm_path(self.cov_db_dir)
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
            "proj_root": False,

            # Flist gen
            "sv_flist_gen_cmd": False,
            "sv_flist_gen_dir": False,
            "sv_flist_gen_opts": False,

            # Build
            "build_dir": False,
            "pre_build_cmds": False,
            "build_cmd": False,
            "build_opts": False,
            "post_build_cmds": False,
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

    cmds_list_vars = ["pre_run_cmds", "post_run_cmds"]

    def __init__(self, index, test, build_job, sim_cfg):
        # Initialize common vars.
        super().__init__(sim_cfg)

        self.target = "run"
        self.pass_patterns = []
        self.fail_patterns = []

        self.mandatory_cmd_attrs.update({
            # tool srcs
            "proj_root": False,
            "uvm_test": False,
            "uvm_test_seq": False,
            "sw_images": False,
            "sw_build_device": False,
            "sw_build_dir": False,
            "run_dir": False,
            "pre_run_cmds": False,
            "run_cmd": False,
            "run_opts": False,
            "post_run_cmds": False,
        })

        self.mandatory_misc_attrs.update({
            "run_dir_name": False,
            "cov_db_dir": False,
            "cov_db_test_dir": False,
            "run_pass_patterns": False,
            "run_fail_patterns": False
        })

        if build_job is not None:
            self.dependencies.append(build_job)

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

    def _on_finish(self, status):
        super()._on_finish(status)
        if status != 'P':
            # Delete the coverage data if available.
            rm_path(self.cov_db_test_dir)

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


class CovUnr(Deploy):
    """
    Abstraction for coverage UNR flow.
    """

    # Register all builds with the class
    items = []

    def __init__(self, sim_cfg):
        # Initialize common vars.
        super().__init__(sim_cfg)

        self.target = "cov_unr"
        self.mandatory_cmd_attrs.update({
            # tool srcs
            "proj_root": False,

            # Need to generate filelist based on build mode
            "sv_flist_gen_cmd": False,
            "sv_flist_gen_dir": False,
            "sv_flist_gen_opts": False,
            "build_dir": False,
            "cov_unr_build_cmd": False,
            "cov_unr_build_opts": False,
            "cov_unr_run_cmd": False,
            "cov_unr_run_opts": False
        })

        self.mandatory_misc_attrs.update({
            "cov_unr_dir": False,
            "build_fail_patterns": False
        })

        super().parse_dict(sim_cfg.__dict__)
        self.__post_init__()

        self.pass_patterns = []
        # Reuse fail_patterns from sim build
        self.fail_patterns = self.build_fail_patterns

        # Start fail message construction
        self.fail_msg = "\n**COV_UNR:** {}<br>\n".format(self.name)
        log_sub_path = self.log.replace(self.sim_cfg.scratch_path + '/', '')
        self.fail_msg += "**LOG:** $scratch_path/{}<br>\n".format(log_sub_path)

        CovUnr.items.append(self)


class CovMerge(Deploy):
    """
    Abstraction for merging coverage databases. An item of this class is created AFTER
    the regression is completed.
    """

    # Register all builds with the class
    items = []

    def __init__(self, run_items, sim_cfg):
        # Initialize common vars.
        super().__init__(sim_cfg)

        self.dependencies += run_items
        self.needs_all_dependencies_passing = False

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
        # Extract cov db dirs from all the sim runs.
        for item in self.dependencies:
            if item.target == "run":
                if item.cov_db_dir not in self.cov_db_dirs:
                    self.cov_db_dirs += item.cov_db_dir + " "

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
            self.cov_db_dirs += " ".join(
                [str(item) for item in prev_cov_db_dirs])

        # Append cov_db_dirs to the list of exports.
        self.exports["cov_db_dirs"] = "\"{}\"".format(self.cov_db_dirs)


class CovReport(Deploy):
    """
    Abstraction for coverage report generation. An item of this class is created AFTER
    the regression is completed.
    """

    # Register all builds with the class
    items = []

    def __init__(self, merge_job, sim_cfg):
        # Initialize common vars.
        super().__init__(sim_cfg)

        self.dependencies.append(merge_job)

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

    def _test_passed(self):
        # Add an extra check to Deploy._test_passed where we extract the
        # coverage results summary for the dashboard (and fail the job if
        # something goes wrong).
        if not super()._test_passed():
            return False

        results, self.cov_total, ex_msg = get_cov_summary_table(
            self.cov_report_txt, self.sim_cfg.tool)

        if ex_msg:
            self.fail_msg += ex_msg
            log.error(ex_msg)
            return False

        # Succeeded in obtaining the coverage data.
        colalign = (("center", ) * len(results[0]))
        self.cov_results = tabulate(results,
                                    headers="firstrow",
                                    tablefmt="pipe",
                                    colalign=colalign)

        # Delete the cov report - not needed.
        rm_path(self.log)
        return True


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
            "proj_root": False,
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
