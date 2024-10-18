# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import datetime
import logging as log
import os
import subprocess
import sys
from Launcher import ErrorMessage
from Launcher import Launcher
from Launcher import LauncherError
from utils import rm_path
from utils import VERBOSE


class NcLauncher(Launcher):
    """Implementation of Launcher to launch jobs using altair nc."""

    def __init__(self, deploy):
        """Initialize common class members."""

        super().__init__(deploy)

        # Popen object when launching the job.
        self.process = None

    def create_run_sh(self, full_path, cmd):
        run_file = os.path.join(full_path, 'run.sh')
        rm_path(run_file)
        lines = ['#!/bin/sh',
                 'function realpath {',
                 '  python -c "import os; print (os.path.realpath(\'$1\'))"',
                 '}',
                 'MY_FILEPATH=$(realpath "${BASH_SOURCE[0]}")',
                 'MY_DIR=$( dirname "${MY_FILEPATH}" )',
                 'cd $MY_DIR',
                 'export TMPDIR=$PWD/tmp',
                 'mkdir -p $TMPDIR',
                 'echo Launch start : `date`',
                 'SECONDS=0',
                 cmd,
                 'echo Launch end : `date`',
                 'echo CPU time : $SECONDS sec']
        with open(run_file, 'w') as f:
            f.write('\n'.join(lines))
        os.chmod(run_file, 0o755)

    def get_submit_cmd(self):
        exetool = self.deploy.sim_cfg.tool
        job_name = self.deploy.full_name
        cmd = self.deploy.cmd
        odir = self.deploy.odir

        # TODO: These tool-specific names need moving into an hjson config
        # file.
        if (exetool == 'xcelium'):
            license_args = ['-r', 'License:Xcelium_Single_Core/1']
        elif (exetool == 'vcs'):
            license_args = ['-r', 'License:VCSRuntime_Net/1']
        else:
            license_args = []
        license_args.extend(['-r', 'RAM/8192', '-r', 'CORES/2'])

        self.create_run_sh(odir, cmd)

        return (['nc', 'run', '-D',
                 '-e', 'SNAPSHOT',
                 '-nodb', '-nolog', '-wl',
                 '-set', job_name] +
                license_args +
                ['--', f'{odir}/run.sh'])

    def _pre_launch(self):
        # start the start_time (correspoinding to job wait time counter)
        super()._pre_launch()
        # hold the start_run_time at 0 (corresponding to job run time counter)
        self.start_run_time = 0

    def _do_launch(self):
        # Compute the environment for the subprocess by overriding environment
        # variables of this process with matching ones from self.deploy.exports
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

        rm_path(self.deploy.get_log_path())
        # using os.open instead of fopen as this allows
        # sharing of file descriptors across processes
        fd = os.open(self.deploy.get_log_path(), os.O_WRONLY | os.O_CREAT)
        fobj = os.fdopen(fd, 'w', encoding='UTF-8')
        os.set_inheritable(fd, True)
        message = '[Executing]:\n{}\n\n'.format(self.deploy.cmd)
        fobj.write(message)
        fobj.flush()
        if self.deploy.sim_cfg.interactive:
            # Interactive: Set RUN_INTERACTIVE to 1
            exports['RUN_INTERACTIVE'] = '1'
            # Line buffering (buf_size = 1) chosen to enable
            # near real time updates from the tool
            buf_size = 1
            std_out = subprocess.PIPE
            std_err = subprocess.STDOUT
        else:
            # setting buf_size = -1 enables subprocess to choose
            # the default buffer size which is more efficient
            buf_size = -1
            std_out = fd
            std_err = fd

        cmd_arr = self.get_submit_cmd()
        log.log(VERBOSE, '[Submitting]:\n{}\n\n'.format(' '.join(cmd_arr)))

        try:
            self.process = subprocess.Popen(cmd_arr,
                                            bufsize=buf_size,
                                            universal_newlines=True,
                                            pass_fds = [fd],
                                            stdout=std_out,
                                            stderr=std_err,
                                            env=exports,
                                            cwd=self.deploy.odir)
            if self.deploy.sim_cfg.interactive:
                for line in self.process.stdout:
                    fobj.write(line)
                    sys.stdout.write(line)
                # Wait until the process exits in case
                # the subprocess closes the stdout but still keeps running
                self.process.wait()
        except subprocess.SubprocessError as e:
            raise LauncherError(f'IO Error: {e}\n'
                                f'See {self.deploy.get_log_path()}')
        finally:
            self._close_process()

        self._link_odir('D')

    def poll(self):
        """Check status of the running process.

        This returns 'D', 'P', 'F', or 'K'. If 'D', the job is still running.
        If 'P', the job finished successfully. If 'F', the job finished with
        an error. If 'K' it was killed.

        This function must only be called after running self.dispatch_cmd() and
        must not be called again once it has returned 'P' or 'F'.
        """

        assert self.process is not None
        if self.process.poll() is None:
            run_timeout_mins = self.deploy.get_timeout_mins()
            wait_timeout_mins = 180  # max wait time in job queue / license
            file_size_thresh_bytes = 5000  # log file size threshold
            if run_timeout_mins is not None and not self.deploy.gui:
                job_waittime = 0
                job_runtime = 0
                # query the log file size
                f_size = os.path.getsize(self.deploy.get_log_path())
                if f_size < file_size_thresh_bytes:
                    # if the job log size is less than the threshold, increment
                    # the job wait time counter. hold the run time counter at 0
                    self.start_run_time = 0
                    elapsed_wait_time = (datetime.datetime.now() -
                                         self.start_time)
                    job_waittime = elapsed_wait_time.total_seconds() / 60
                else:
                    # if the job log size is more than the threshold, start the
                    # the job run time counter if has not already started.
                    # Hold the wait time counter at the last updated value
                    if (self.start_run_time == 0):
                        self.start_run_time = datetime.datetime.now()
                    elapsed_wait_time = (self.start_run_time -
                                         self.start_time)
                    job_waittime = elapsed_wait_time.total_seconds() / 60
                # if the job run time counter has already started, increment
                # the job run time counter
                if (self.start_run_time != 0):
                    elapsed_run_time = (datetime.datetime.now() -
                                        self.start_run_time)
                    job_runtime = elapsed_run_time.total_seconds() / 60
                # if the job run has not started within the max time specified
                # in this file or if the job has been running for longer than
                # the time specified in the block json or via dvsim switches
                # terminate it and send the appropriate error message
                wait_timeout = (job_waittime > wait_timeout_mins)
                run_timeout = (job_runtime > run_timeout_mins)
                if run_timeout or wait_timeout:
                    self._kill()
                    if run_timeout:
                        timeout_message = f'Job timed out after running ' \
                                          f'{run_timeout_mins} mins'
                    if wait_timeout:
                        timeout_message = f'Job timed out after waiting ' \
                                          f'{wait_timeout_mins} mins'
                    self._post_finish('K',
                                      ErrorMessage(line_number=None,
                                                   message=timeout_message,
                                                   context=[timeout_message]))
                    return 'K'
                else:
                    return 'D'
            else:
                return 'D'

        self.exit_code = self.process.returncode
        status, err_msg = self._check_status()
        self._post_finish(status, err_msg)
        return self.status

    def _kill(self):
        """Kill the running process.

        Try to kill the running process. Send SIGTERM
        and SIGKILL.
        """
        try:
            log.log(VERBOSE, f'[Stopping] : {self.deploy.full_name}')
            subprocess.run(['nc', 'stop', '-set', self.deploy.full_name,
                            '-sig', 'TERM,KILL'],
                           check=True,
                           stdout=subprocess.PIPE,
                           stderr=subprocess.PIPE)
        except subprocess.CalledProcessError as e:
            log.error('Failed to kill job: {}'.format(
                e.stderr.decode('utf-8').strip()))

    def kill(self):
        """Kill the running process.

        This must be called between dispatching and reaping the process (the
        same window as poll()).

        """
        self._kill()
        self._post_finish(
            'K',
            ErrorMessage(line_number=None, message='Job killed!', context=[]))

    def _post_finish(self, status, err_msg):
        self._close_process()
        self.process = None
        super()._post_finish(status, err_msg)

    def _close_process(self):
        """Close the file descriptors associated with the process."""

        assert self.process
        if self.process.stdout:
            self.process.stdout.close()
