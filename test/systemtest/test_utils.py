#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import difflib
import filecmp
import inspect
import logging
import os
import re
import select
import shlex
import signal
import subprocess
import time


class Process:
    """Utility class used to spawn an interact with processs.s"""
    def __init__(self,
                 cmd,
                 logdir,
                 cwd=None,
                 startup_done_expect=None,
                 startup_timeout=None):
        """Creates Process instance.

        Args:
            cmd: Command line argument used to spawn process.
            logdir: Directory used to store STDOUT and STDERR output.
            cwd: Working directory used to spawn process.
            startup_done_expect: Pattern used to check at process startup time.
            startup_timeout: Timeout in seconds for |startup_done_expect| check.
        """
        if isinstance(cmd, str):
            self.cmd = shlex.split(cmd)
        else:
            self.cmd = cmd
        self.logdir = logdir
        self.cwd = cwd
        self.startup_done_expect = startup_done_expect
        self.startup_timeout = startup_timeout
        self.proc = None
        self.logger = logging.getLogger(__name__)

        self._f_stdout = None
        self._f_stderr = None
        self._f_stdout_r = None
        self._f_stderr_r = None

    def __del__(self):
        try:
            self.proc.kill()
            self._f_stdout.close()
            self._f_stderr.close()
            self._f_stdout_r.close()
            self._f_stderr_r.close()
        except:
            pass

    def run(self):
        """Start process with command line configured in constructor."""
        cmd_name = os.path.basename(self.cmd[0])

        # Enforce line-buffered STDOUT even when sending STDOUT/STDERR to file.
        # If applications don't fflush() STDOUT manually, STDOUT goes through
        # a 4kB buffer before we see any output, which prevents searching for
        # the string indicating a successful startup.
        # see discussion at http://www.pixelbeat.org/programming/stdio_buffering/
        cmd = ['stdbuf', '-oL'] + self.cmd
        self.logger.info("Running command " + ' '.join(cmd))

        logfile_stdout = os.path.join(self.logdir,
                                      "{}.stdout".format(cmd_name))
        logfile_stderr = os.path.join(self.logdir,
                                      "{}.stderr".format(cmd_name))
        self.logger.debug("Capturing STDOUT at " + logfile_stdout)
        self.logger.debug("Capturing STDERR at " + logfile_stderr)

        self._f_stdout = open(logfile_stdout, 'w')
        self._f_stderr = open(logfile_stderr, 'w')
        self.proc = subprocess.Popen(cmd,
                                     cwd=self.cwd,
                                     universal_newlines=True,
                                     bufsize=1,
                                     stdin=subprocess.PIPE,
                                     stdout=self._f_stdout,
                                     stderr=self._f_stderr)

        self._f_stdout_r = open(logfile_stdout, 'r')
        self._f_stderr_r = open(logfile_stderr, 'r')

        # no startup match pattern given => startup done!
        if self.startup_done_expect == None:
            return True

        # check if the string indicating a successful startup appears in the
        # the program output (STDOUT or STDERR)
        init_done = self.find_in_output(pattern=self.startup_done_expect,
                                        timeout=self.startup_timeout)

        if init_done == None:
            raise subprocess.TimeoutExpired

        self.logger.info("Startup sequence matched, startup done.")

        return True

    def terminate(self):
        """Terminates process started by run call."""
        if not self.proc:
            return
        self.proc.terminate()

    def send_ctrl_c(self):
        """Sends SIGINT to process started by run call."""
        if not self.proc:
            return
        self.proc.send_signal(signal.SIGINT)

    def expect(self, stdin_data=None, pattern=None, timeout=None):
        """Write send to STDIN and check if the output is as expected.

        Args:
            stdin_data: Data to send to STDIN.
            pattern: Pattern to search for after sending |stdin_data|.
            timeout: Timeout in seconds for |pattern| check.
        Returns:
            True if |pattern| found, False otherwise.
        """
        # We don't get STDOUT/STDERR from subprocess.communicate() as it's
        # redirected to file. We need to read the files instead.

        # XXX: races (false positives) can happen here if output is generated
        # before the input is sent to the process.
        if pattern == None:
            self._f_stdout_r.seek(0, 2)

        self.proc.stdin.write(stdin_data)
        self.proc.stdin.flush()

        if pattern == None:
            return True

        return self.find_in_output(pattern, timeout) != None

    def find_in_output(self, pattern, timeout):
        """Read STDOUT and STDERR to find an expected pattern.

        Both streams are reset to the start of the stream before searching.
        pattern can be of two types:
        1. A regular expression (a re object). In this case, the pattern is
           matched against all lines and the result of re.match(pattern) is
           returned. Multi-line matches are not supported.
        2. A string. In this case pattern is compared to each line with
           startswith(), and the full matching line is returned on a match.
        If no match is found None is returned.
        timeout is given in seconds.

        Args:
            pattern: Pattern to search for in STDOUT or STDERR.
            timeout: Timeout in seconds for |pattern| check.
        Returns:
            String containing |pattern|, None otherwise.
        """

        if timeout != None:
            t_end = time.time() + timeout

        # reset streams
        self._f_stdout_r.seek(0)
        self._f_stderr_r.seek(0)

        while True:
            # check STDOUT as long as there is one
            i = 0
            for line in self._f_stdout_r:
                i += 1
                if hasattr(pattern, "match"):
                    m = pattern.match(line)
                    if m:
                        return m
                else:
                    if line.startswith(pattern):
                        return line

                # Check if we exceed the timeout while reading from STDOUT
                # do so only every 100 lines to reduce the performance impact.
                if timeout != None and i % 100 == 99 and time.time() >= t_end:
                    break

            # check STDERR as long as there is one
            i = 0
            for line in self._f_stderr_r:
                i += 1
                if hasattr(pattern, "match"):
                    m = pattern.match(line)
                    if m:
                        return m
                else:
                    if line.startswith(pattern):
                        return line

                # Check if we exceed the timeout while reading from STDERR
                # do so only every 100 lines to reduce the performance impact.
                if timeout != None and i % 100 == 99 and time.time() >= t_end:
                    break

            # wait for 200ms for new output
            if timeout != None:
                try:
                    self.proc.wait(timeout=0.2)
                except subprocess.TimeoutExpired:
                    pass

        return None


def stream_fd_to_log(fd, logger, pattern, timeout=None):
    """
    Streams lines from the given fd to log until pattern matches.

    Returns the match object derived from pattern.match(), or None if
    the timeout expires.
    """

    deadline = None
    if timeout != None:
        deadline = time.monotonic() + timeout

    os.set_blocking(fd, False)
    line_of_output = b''
    while True:
        curtime = time.monotonic()
        if deadline != None and curtime > deadline:
            return None

        if line_of_output.endswith(b'\n'):
            line_of_output = b''

        # select() on the fd so that we don't waste time reading when
        # we wouldn't get anything out of it.
        if deadline != None:
            rlist, _, _ = select.select([fd], [], [],
                                        deadline - curtime)
        else:
            rlist, _, _ = select.select([fd], [], [])

        if len(rlist) == 0:
            continue

        raw_bytes = os.read(fd, 1024)
        lines = raw_bytes.splitlines(True)

        for line in lines:
            line_of_output += line
            if not line_of_output.endswith(b'\n'):
                break

            logger.debug('fd#%d: %s' % (fd, line_of_output))
            match = pattern.match(line_of_output.decode('utf-8'))
            if match != None:
              return match

            line_of_output = b''

# If logfile option was given, log all outputs to file.
def setup_logfile(logger, logfile):
    if logfile:
        logger.debug("Logfile at %s" % (logfile))
        logger.setLevel(logging.DEBUG)
        fh = logging.FileHandler(filename=logfile, mode='w')
        fh.setLevel(logging.DEBUG)
        logger.addHandler(fh)
