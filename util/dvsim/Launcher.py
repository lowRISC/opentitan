# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import collections
import logging as log
import os
import re
import sys
from pathlib import Path

from utils import VERBOSE, clean_odirs, mk_symlink, rm_path


class LauncherError(Exception):
    def __init__(self, msg):
        self.msg = msg


class ErrorMessage(
        collections.namedtuple(
            'ErrorMessage',
            ['line_number', 'message', 'context'],
        )):
    """Contains error-related information.

    This support classification of failures into buckets. The message field
    is used to generate the bucket, and context contains a list of lines in
    the failing log that can be useful for quick diagnostics.
    """
    pass


class Launcher:
    """
    Abstraction for launching and maintaining a job.

    An abstract class that provides methods to prepare a job's environment,
    launch the job, poll for its completion and finally do some cleanup
    activities. This class is not meant to be instantiated directly. Each
    launcher object holds an instance of the deploy object.
    """

    # Type of launcher used as string.
    variant = None

    # Max jobs running at one time
    max_parallel = sys.maxsize

    # Max jobs polled at one time
    max_poll = 10000

    # Poll job's completion status every this many seconds
    poll_freq = 1

    # Points to the python virtual env area.
    pyvenv = None

    # If a history of previous invocations is to be maintained, then keep no
    # more than this many directories.
    max_odirs = 5

    # Flag indicating the workspace preparation steps are complete.
    workspace_prepared = False
    workspace_prepared_for_cfg = set()

    @staticmethod
    def set_pyvenv(project):
        '''Activate a python virtualenv if available.

        The env variable <PROJECT>_PYTHON_VENV if set, points to the path
        containing the python virtualenv created specifically for this
        project. We can activate it if needed, before launching jobs using
        external compute machines.

        This is not applicable when running jobs locally on the user's machine.
        '''

        if Launcher.pyvenv is not None:
            return

        # If project-specific python virtualenv path is set, then activate it
        # before running downstream tools. This is more relevant when not
        # launching locally, but on external machines in a compute farm, which
        # may not have access to the default python installation area on the
        # host machine.
        #
        # The code below allows each launcher variant to set its own virtualenv
        # because the loading / activating mechanism could be different between
        # them.
        Launcher.pyvenv = os.environ.get("{}_PYVENV_{}".format(
            project.upper(), Launcher.variant.upper()))

        if not Launcher.pyvenv:
            Launcher.pyvenv = os.environ.get("{}_PYVENV".format(
                project.upper()))

    @staticmethod
    def prepare_workspace(project, repo_top, args):
        '''Prepare the workspace based on the chosen launcher's needs.

        This is done once for the entire duration for the flow run.
        'project' is the name of the project.
        'repo_top' is the path to the repository.
        'args' are the command line args passed to dvsim.
        '''
        pass

    @staticmethod
    def prepare_workspace_for_cfg(cfg):
        '''Prepare the workspace for a cfg.

        This is invoked once for each cfg.
        'cfg' is the flow configuration object.
        '''
        pass

    def __str__(self):
        return self.deploy.full_name + ":launcher"

    def __init__(self, deploy):
        cfg = deploy.sim_cfg

        # One-time preparation of the workspace.
        if not Launcher.workspace_prepared:
            self.prepare_workspace(cfg.project, cfg.proj_root, cfg.args)
            Launcher.workspace_prepared = True

        # One-time preparation of the workspace, specific to the cfg.
        if cfg not in Launcher.workspace_prepared_for_cfg:
            self.prepare_workspace_for_cfg(cfg)
            Launcher.workspace_prepared_for_cfg.add(cfg)

        # Store the deploy object handle.
        self.deploy = deploy

        # Status of the job. This is primarily determined by the
        # _check_status() method, but eventually updated by the _post_finish()
        # method, in case any of the cleanup tasks fails. This value is finally
        # returned to the Scheduler by the poll() method.
        self.status = None

        # Return status of the process running the job.
        self.exit_code = None

        # Flag to indicate whether to 'overwrite' if odir already exists,
        # or to backup the existing one and create a new one.
        # For builds, we want to overwrite existing to leverage the tools'
        # incremental / partition compile features. For runs, we may want to
        # create a new one.
        self.renew_odir = False

    def _make_odir(self):
        """Create the output directory."""

        # If renew_odir flag is True - then move it.
        if self.renew_odir:
            clean_odirs(odir=self.deploy.odir, max_odirs=self.max_odirs)
        os.makedirs(self.deploy.odir, exist_ok=True)

    def _link_odir(self, status):
        """Soft-links the job's directory based on job's status.

        The dispatched, passed and failed directories in the scratch area
        provide a quick way to get to the job that was executed.
        """

        dest = Path(self.deploy.sim_cfg.links[status], self.deploy.qual_name)
        mk_symlink(self.deploy.odir, dest)

        # Delete the symlink from dispatched directory if it exists.
        if status != "D":
            old = Path(self.deploy.sim_cfg.links['D'], self.deploy.qual_name)
            rm_path(old)

    def _dump_env_vars(self, exports):
        """Write env vars to a file for ease of debug.

        Each extended class computes the list of exports and invokes this
        method right before launching the job.
        """

        with open(self.deploy.odir + "/env_vars",
                  "w",
                  encoding="UTF-8",
                  errors="surrogateescape") as f:
            for var in sorted(exports.keys()):
                f.write("{}={}\n".format(var, exports[var]))

    def _pre_launch(self):
        """Do pre-launch activities.

        Examples include such as preparing the job's environment, clearing
        old runs, creating the output directory, dumping all env variables
        etc. This method is already invoked by launch() as the first step.
        """

        self.deploy.pre_launch()
        self._make_odir()

    def _do_launch(self):
        """Launch the job."""

        raise NotImplementedError()

    def launch(self):
        """Launch the job."""

        self._pre_launch()
        self._do_launch()

    def poll(self):
        """Poll the launched job for completion.

        Invokes _check_status() and _post_finish() when the job completes.
        """

        raise NotImplementedError()

    def kill(self):
        """Terminate the job."""

        raise NotImplementedError()

    def _check_status(self):
        """Determine the outcome of the job (P/F if it ran to completion).

        Returns (status, err_msg) extracted from the log, where the status is
        "P" if the it passed, "F" otherwise. This is invoked by poll() just
        after the job finishes. err_msg is an instance of the named tuple
        ErrorMessage.
        """
        def _find_patterns(patterns, line):
            """Helper function that returns the pattern if any of the given
            patterns is found, else None."""

            assert patterns
            for pattern in patterns:
                match = re.search(r"{}".format(pattern), line)
                if match:
                    return pattern
            return None

        if self.deploy.dry_run:
            return "P", None

        # Only one fail pattern needs to be seen.
        chk_failed = bool(self.deploy.fail_patterns)

        # All pass patterns need to be seen, so we replicate the list and remove
        # patterns as we encounter them.
        pass_patterns = self.deploy.pass_patterns.copy()
        chk_passed = bool(pass_patterns) and (self.exit_code == 0)

        try:
            with open(self.deploy.get_log_path(),
                      "r",
                      encoding="UTF-8",
                      errors="surrogateescape") as f:
                lines = f.readlines()
        except OSError as e:
            return "F", ErrorMessage(
                line_number=None,
                message="Error opening file {}:\n{}".format(
                    self.deploy.get_log_path(), e),
                context=[],
            )

        if chk_failed or chk_passed:
            for cnt, line in enumerate(lines):
                if chk_failed:
                    if _find_patterns(self.deploy.fail_patterns, line):
                        # If failed, then nothing else to do. Just return.
                        # Privide some extra lines for context.
                        return "F", ErrorMessage(line_number=cnt + 1,
                                                 message=line.strip(),
                                                 context=lines[cnt:cnt + 5])

                if chk_passed:
                    pattern = _find_patterns(pass_patterns, line)
                    if pattern:
                        pass_patterns.remove(pattern)
                        chk_passed = bool(pass_patterns)

        # If no fail patterns were seen, but the job returned with non-zero
        # exit code for whatever reason, then show the last 10 lines of the log
        # as the failure message, which might help with the debug.
        if self.exit_code != 0:
            return "F", ErrorMessage(line_number=None,
                                     message="Job returned non-zero exit code",
                                     context=lines[-10:])
        if chk_passed:
            return "F", ErrorMessage(
                line_number=None,
                message=f"Some pass patterns missing: {pass_patterns}",
                context=lines[-10:],
            )
        return "P", None

    def _post_finish(self, status, err_msg):
        """Do post-completion activities, such as preparing the results.

        Must be invoked by poll(), after the job outcome is determined.

        status is the status of the job, either 'P', 'F' or 'K'.
        err_msg is an instance of the named tuple ErrorMessage.
        """

        assert status in ['P', 'F', 'K']
        self._link_odir(status)
        log.debug("Item %s has completed execution: %s", self, status)

        try:
            # Run the target-specific cleanup tasks regardless of the job's
            # outcome.
            self.deploy.post_finish(status)
        except Exception as e:
            # If the job had already failed, then don't do anything. If it's
            # cleanup task failed, then mark the job as failed.
            if status == "P":
                status = "F"
                err_msg = ErrorMessage(line_number=None,
                                       message=f"{e}",
                                       context=[])

        self.status = status
        if self.status != "P":
            assert err_msg and isinstance(err_msg, ErrorMessage)
            self.fail_msg = err_msg
            log.log(VERBOSE, err_msg.message)
