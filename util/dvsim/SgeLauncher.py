# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
# ------------------------------------
#      SgeLauncher Class
#
# ------------------------------------
import os
import shlex
import subprocess
from subprocess import PIPE, Popen

import SGE
from Launcher import ErrorMessage, Launcher, LauncherError

global job_name

pid = os.getpid()


class SgeLauncher(Launcher):
    """
    Implementation of Launcher to launch jobs in the user's local workstation.
    """

    # Misc common SgeLauncher settings.
    max_odirs = 5

    def __init__(self, deploy):
        '''Initialize common class members.'''

        super().__init__(deploy)

        # Popen object when launching the job.
        self.process = None

    def _do_launch(self):
        global job_name
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

        try:
            f = open(self.deploy.get_log_path(),
                     "w",
                     encoding="UTF-8",
                     errors="surrogateescape")
            f.write("[Executing]:\n{}\n\n".format(self.deploy.cmd))
            f.flush()
            # ---------- prepare SGE job struct -----
            sgeJob = SGE.qsubOptions()
            sgeJob.args.N = 'VCS_RUN_' + str(pid)  # Name of Grid Engine job
            if "build.log" in self.deploy.get_log_path():
                sgeJob.args.N = 'VCS_BUILD_' + str(
                    pid)  # Name of Grid Engine job

            job_name = sgeJob.args.N
            sgeJob.args.t = '0'  # Define an array job with 20 subjobs
            sgeJob.args.slot = '1'  # Define num of slot
            sgeJob.args.sync = 'y'  # wait for job to complete before exiting
            sgeJob.args.q = 'vcs_q'  # Define the sge queue name
            sgeJob.args.p = '0'  # Set priority to 0
            sgeJob.args.ll = 'mf=20G'  # memory req,request the given resources
            # pecifies a range of priorities from -1023 to 1024.
            # The higher the number, the higher the priority.
            # The default priority for jobs is zero
            sgeJob.args.command = '"' + self.deploy.cmd + '"'
            sgeJob.args.b = 'y'  # This is a binary file
            sgeJob.args.o = self.deploy.get_log_path() + '.sge'
            cmd = str(sgeJob.execute(mode='echo'))
            print('INFO: SGE command line : "' + str(cmd) + '"')
            # ---------------
            self.process = subprocess.Popen(shlex.split(cmd),
                                            bufsize=4096,
                                            universal_newlines=True,
                                            stdout=f,
                                            stderr=f,
                                            env=exports)
            f.close()
        except subprocess.SubprocessError as e:
            raise LauncherError('IO Error: {}\nSee {}'.format(
                e, self.deploy.get_log_path()))
        finally:
            self._close_process()

        self._link_odir("D")
        f.close()

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
        # -------------------------------------
        # copy SGE jobb results to log file
        if os.path.exists(self.deploy.get_log_path() + '.sge'):

            file1 = open(self.deploy.get_log_path() + '.sge', 'r', errors='replace')
            Lines = file1.readlines()
            file1.close()
            f = open(self.deploy.get_log_path(),
                     "a",
                     encoding="UTF-8",
                     errors="surrogateescape")
            for line in Lines:
                f.write(line)
            f.flush()
            os.remove(self.deploy.get_log_path() + '.sge')
            f.close()
        # -------------------------------------

        self.exit_code = self.process.returncode
        status, err_msg = self._check_status()
        self._post_finish(status, err_msg)
        return status

    def kill(self):
        global job_name
        '''Kill the running process.

        This must be called between dispatching and reaping the process (the
        same window as poll()).

        '''
        assert self.process is not None

        # Try to kill the running process. Send SIGTERM first, wait a bit,
        # and then send SIGKILL if it didn't work.
        self.process.terminate()
        try:
            self.process.wait(timeout=2)
        except subprocess.TimeoutExpired:
            self.process.kill()
            # ----------------------------
            # qdel -f kill sge job_name
            cmd = 'qstatus -a | grep ' + job_name
            with Popen(cmd, stdout=PIPE, stderr=None, shell=True) as process:
                output = process.communicate()[0].decode("utf-8")
                output = output.rstrip("\n")
                if output != '':
                    output_l = output.split()
                    cmd = 'qdel ' + output_l[0]
                    with Popen(cmd, stdout=PIPE, stderr=None,
                               shell=True) as process:
                        output = process.communicate()[0].decode("utf-8")
                        output = output.rstrip("\n")
                        print('Killed job "' + str(output) + '"')
            # ----------------------------
        self._post_finish(
            'K',
            ErrorMessage(line_number=None, message='Job killed!', context=[]))

    def _post_finish(self, status, err_msg):
        super()._post_finish(status, err_msg)
        self._close_process()
        self.process = None

    def _close_process(self):
        '''Close the file descriptors associated with the process.'''

        assert self.process
        if self.process.stdout:
            self.process.stdout.close()
