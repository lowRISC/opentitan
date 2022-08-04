# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import logging as log
import os
import re
import subprocess
import tarfile
from pathlib import Path

from Launcher import ErrorMessage, Launcher, LauncherError
from utils import VERBOSE, clean_odirs


class LsfLauncher(Launcher):

    # A hidden directory specific to a cfg, where we put individual 'job'
    # scripts.
    jobs_dir = {}

    # All launcher instances available for lookup.
    jobs = {}

    # When the job completes, we try to read the job script output to determine
    # the outcome. It may not have been completely written the first time we
    # read it so we retry on the next poll, no more than 10 times.
    max_poll_retries = 10

    # TODO: Add support for build/run/cov job specific resource requirements:
    #       cpu, mem, disk, stack.
    # TODO: Allow site-specific job resource usage setting using
    #       `DVSIM_LSF_CFG` environment variable.

    @staticmethod
    def prepare_workspace(project, repo_top, args):
        # Since we dispatch to remote machines, a project specific python
        # virtualenv is exists, needs to be activated when launching the job.
        Launcher.set_pyvenv(project)
        if Launcher.pyvenv is None:
            return

        # If it is already a dir, then nothing to be done.
        if os.path.isdir(Launcher.pyvenv):
            return

        # If not, then it needs to be a valid tarball. Extract it in the
        # scratch area if it does not exist.
        stem = Path(Launcher.pyvenv).stem
        if stem.endswith("tar"):
            stem = stem[:-4]
        path = Path(args.scratch_root, stem)
        if not path.is_dir():
            log.info("[prepare_workspace]: [pyvenv]: Extracting %s",
                     Launcher.pyvenv)
            with tarfile.open(Launcher.pyvenv, mode='r') as tar:
                tar.extractall(args.scratch_root)
            log.info("[prepare_workspace]: [pyvenv]: Done: %s", path)
        Launcher.pyvenv = path

    @staticmethod
    def prepare_workspace_for_cfg(cfg):
        # Create the job dir.
        LsfLauncher.jobs_dir[cfg] = Path(cfg.scratch_path, "lsf",
                                         cfg.timestamp)
        clean_odirs(odir=LsfLauncher.jobs_dir[cfg], max_odirs=2)
        os.makedirs(Path(LsfLauncher.jobs_dir[cfg]), exist_ok=True)

    @staticmethod
    def make_job_script(cfg, job_name):
        """Creates the job script.

        Once all jobs in the array are launched, the job script can be created.
        It is a bash script that takes the job index as a single argument.
        This index is set in the bsub command as '$LSB_JOBINDEX', which bsub
        sets as the actual index when launching that job in the array. This
        script is super simple - it is just a giant case statement that
        switches on the job index to run that specific job. This preferred over
        creating individual scripts for each job which incurs additional file
        I/O overhead when the scratch area is on NFS, causing a slowdown.

        Returns the path to the job script.
        """

        lines = ["#!/usr/bin/env bash\nset -e\n"]

        # Activate the python virtualenv if it exists.
        if Launcher.pyvenv:
            lines += ["source {}/bin/activate\n".format(Launcher.pyvenv)]

        lines += ["case $1 in\n"]
        for job in LsfLauncher.jobs[cfg][job_name]:
            # Redirect the job's stdout and stderr to its log file.
            cmd = "{} > {} 2>&1".format(job.deploy.cmd,
                                        job.deploy.get_log_path())
            lines += ["  {})\n".format(job.index), "    {};;\n".format(cmd)]

        # Throw error as a sanity check if the job index is invalid.
        lines += [
            "  *)\n",
            "    echo \"ERROR: Illegal job index: $1\" 1>&2; exit 1;;\n",
            "esac\n"
        ]
        if Launcher.pyvenv:
            lines += ["deactivate\n"]

        job_script = Path(LsfLauncher.jobs_dir[cfg], job_name)
        try:
            with open(job_script, "w", encoding='utf-8') as f:
                f.writelines(lines)
        except IOError as e:
            err_msg = "ERROR: Failed to write {}:\n{}".format(job_script, e)
            LsfLauncher._post_finish_job_array(cfg, job_name, err_msg)
            raise LauncherError(err_msg)

        log.log(VERBOSE, "[job_script]: %s", job_script)
        return job_script

    def __init__(self, deploy):
        super().__init__(deploy)

        # Maintain the job script output as an instance variable for polling
        # and cleanup.
        self.bsub_out = None

        # If we already opened the job script output file (but have not
        # determined the outcome), then we maintain the file descriptor rather
        # then reopening it and starting all over again on the next poll.
        self.bsub_out_fd = None
        self.bsub_out_err_msg = []
        self.bsub_out_err_msg_found = False

        # Set the job id.
        self.job_id = None

        # Polling retry counter..
        self.num_poll_retries = 0

        # Add self to the list of jobs.
        cfg_dict = LsfLauncher.jobs.setdefault(deploy.sim_cfg, {})
        job_name_list = cfg_dict.setdefault(deploy.job_name, [])
        job_name_list.append(self)

        # Job's index in the array.
        self.index = len(job_name_list)

    def _do_launch(self):
        # Add self to the list of jobs.
        job_name = self.deploy.job_name
        cfg = self.deploy.sim_cfg
        job_total = len(LsfLauncher.jobs[cfg][job_name])

        # The actual launching of the bsub command cannot happen until the
        # Scheduler has dispatched ALL jobs in the array.
        if self.index < job_total:
            return

        job_script = self.make_job_script(cfg, job_name)

        # Update the shell's env vars with self.exports. Values in exports must
        # replace the values in the shell's env vars if the keys match.
        exports = os.environ.copy()
        if self.deploy.exports:
            exports.update(self.deploy.exports)

        # Clear the magic MAKEFLAGS variable from exports if necessary. This
        # variable is used by recursive Make calls to pass variables from one
        # level to the next. Here, self.cmd is a call to Make but it's
        # logically a top-level invocation: we don't want to pollute the flow's
        # Makefile with Make variables from any wrapper that called dvsim.
        if 'MAKEFLAGS' in exports:
            del exports['MAKEFLAGS']

        self._dump_env_vars(exports)

        # TODO: Arbitrarily set the max slot-limit to 100.
        job_array = "{}[1-{}]".format(job_name, job_total)
        if job_total > 100:
            job_array += "%100"

        # TODO: This needs to be moved to a HJson.
        if self.deploy.sim_cfg.tool == "vcs":
            job_rusage = "\'rusage[vcssim=1,vcssim_dynamic=1:duration=1]\'"

        elif self.deploy.sim_cfg.tool == "xcelium":
            job_rusage = "\'rusage[xcelium=1,xcelium_dynamic=1:duration=1]\'"

        else:
            job_rusage = None

        # Launch the job array.
        cmd = [
            "bsub",
            # TODO: LSF project name could be site specific!
            "-P",
            cfg.project,
            "-J",
            job_array,
            "-oo",
            "{}.%I.out".format(job_script),
            "-eo",
            "{}.%I.out".format(job_script)
        ]
        if self.deploy.get_timeout_mins():
            cmd += ["-c", self.deploy.get_timeout_mins()]

        if job_rusage:
            cmd += ["-R", job_rusage]

        cmd += ["/usr/bin/bash {} $LSB_JOBINDEX".format(job_script)]

        try:
            p = subprocess.run(cmd,
                               check=True,
                               timeout=60,
                               stdout=subprocess.PIPE,
                               stderr=subprocess.PIPE,
                               env=exports)
        except subprocess.CalledProcessError as e:
            # Need to mark all jobs in this range with this fail pattern.
            err_msg = e.stderr.decode("utf-8").strip()
            self._post_finish_job_array(cfg, job_name, err_msg)
            raise LauncherError(err_msg)

        # Extract the job ID.
        result = p.stdout.decode("utf-8").strip()
        job_id = result.split('Job <')[1].split('>')[0]
        if not job_id:
            self._post_finish_job_array(cfg, job_name, "Job ID not found!")
            raise LauncherError(err_msg)

        for job in LsfLauncher.jobs[cfg][job_name]:
            job.bsub_out = Path("{}.{}.out".format(job_script, job.index))
            job.job_id = "{}[{}]".format(job_id, job.index)
            job._link_odir("D")

    def poll(self):
        # It is possible we may have determined the status already.
        if self.status:
            return self.status

        if not self.bsub_out_fd:
            # If job id is not set, the bsub command has not been sent yet.
            if not self.job_id:
                return 'D'

            # We redirect the job's output to the log file, so the job script
            # output remains empty until the point it finishes. This is a very
            # quick way to check if the job has completed. If nothing has been
            # written to the job script output yet (or if it is not yet
            # created), then the job is still running.
            try:
                if not self.bsub_out.stat().st_size:
                    return "D"
            except FileNotFoundError:
                return "D"

            # If we got to this point,  we can now open the job script output
            # file for reading.
            try:
                self.bsub_out_fd = open(self.bsub_out, "r")
            except IOError as e:
                self._post_finish(
                    "F",
                    ErrorMessage(
                        line_number=None,
                        message="ERROR: Failed to open {}\n{}.".format(
                            self.bsub_out, e),
                        context=[e]))
                return "F"

        # Now that the job has completed, we need to determine its status.
        #
        # If the job successfully launched and it failed, the failure message
        # will appear in its log file (because of the stderr redirection).
        # But, in some cases, if there is something wrong with the command
        # itself, bsub might return immediately with an error message, which
        # will appear in the job script output file. We want to retrieve that
        # so that we can report the status accurately.
        #
        # At this point, we could run bjobs or bhist to determine the status,
        # but it has been found to be too slow, expecially when running 1000s
        # of jobs. Plus, we have to read the job script output anyway to look
        # for those error messages.
        #
        # So we just read this file to determine both, the status and extract
        # the error message, rather than running bjobs or bhist. But there is
        # one more complication to deal with - if we read the file now, it is
        # possible that it may not have been fully updated. We will try reading
        # it anyway. If we are unable to find what we are looking for, then we
        # will resume reading it again at the next poll. We will do this upto
        # max_poll_retries times before giving up and flagging an error.
        #
        # TODO: Consider using the IBM Plarform LSF Python APIs instead.
        #       (deferred due to shortage of time / resources).
        # TODO: Parse job telemetry data for performance insights.

        exit_code = self._get_job_exit_code()
        if exit_code is not None:
            self.exit_code = exit_code
            status, err_msg = self._check_status()
            # Prioritize error messages from bsub over the job's log file.
            if self.bsub_out_err_msg:
                err_msg = ErrorMessage(line_number=None,
                                       message=self.bsub_out_err_msg,
                                       context=[self.bsub_out_err_msg])
            self._post_finish(status, err_msg)
            return status

        else:
            self.num_poll_retries += 1
            # Fail the test if we have reached the max polling retries.
            if self.num_poll_retries == LsfLauncher.max_poll_retries:
                self._post_finish(
                    "F", "ERROR: Reached max retries while "
                    "reading job script output {} to determine"
                    " the outcome.".format(self.bsub_out))
                return "F"

        return "D"

    def _get_job_exit_code(self):
        '''Read the job script output to retrieve the exit code.

        Also read the error message if any, which will appear at the beginning
        of the log file followed by bsub's standard 'email' format output. It
        looks something like this:

            <stderr messages>
            ------------------------------------------------------------
            Sender: LSF System <...>
            Subject: ...
            ...

            Successfully completed.
            <OR>
            Exited with exit code 1.

            ...

        The extracted stderr messages are logged to self.fail_msg. The line
        indicating whether it was successful or it failed with an exit code
        is used to return the exit code.

        Returns the exit code if found, else None.
        '''

        # Job script output must have been opened already.
        assert self.bsub_out_fd

        for line in self.bsub_out_fd:
            if not self.bsub_out_err_msg_found:
                m = re.match("^Sender", line)
                if m:
                    # Pop the line before the sender line.
                    self.bsub_out_err_msg = "\n".join(
                        self.bsub_out_err_msg[:-1])
                    self.bsub_out_err_msg_found = True
                else:
                    self.bsub_out_err_msg.append(line.strip())

            else:
                m = re.match(r"^Exited with exit code (\d+).\n$", line)
                if m:
                    return m.group(1)

                if not self.bsub_out_err_msg:
                    m = re.match(r"^Successfully completed.\n$", line)
                    if m:
                        return 0
        return None

    def kill(self):
        if self.job_id:
            try:
                subprocess.run(["bkill", "-s", "SIGTERM", self.job_id],
                               check=True,
                               stdout=subprocess.PIPE,
                               stderr=subprocess.PIPE)
            except subprocess.CalledProcessError as e:
                log.error("Failed to kill job: {}".format(
                    e.stderr.decode("utf-8").strip()))
        else:
            log.error("Job ID for %s not found", self.deploy.full_name)

        self._post_finish('K', "Job killed!")

    def _post_finish(self, status, err_msg):
        if self.bsub_out_fd:
            self.bsub_out_fd.close()
        if self.exit_code is None:
            self.exit_code = 0 if status == 'P' else 1
        super()._post_finish(status, err_msg)

    @staticmethod
    def _post_finish_job_array(cfg, job_name, err_msg):
        '''On LSF error, mark all jobs in this array as killed.

        err_msg is the error message indicating the cause of failure.'''

        for job in LsfLauncher.jobs[cfg][job_name]:
            job._post_finish(
                'F', ErrorMessage(line_number=None,
                                  message=err_msg,
                                  context=[err_msg]))
