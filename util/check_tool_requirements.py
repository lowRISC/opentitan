#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
from distutils.version import StrictVersion
import logging as log
import os
import re
import shlex
import subprocess
import sys

# Display INFO log messages and up.
log.basicConfig(level=log.INFO, format="%(levelname)s: %(message)s")


def get_tool_requirements_path():
    '''Return the path to tool_requirements.py, at the top of the repo'''
    # top_src_dir is the top of the repository
    top_src_dir = os.path.normpath(os.path.join(os.path.dirname(__file__),
                                                '..'))

    return os.path.join(top_src_dir, 'tool_requirements.py')


class ReqErr(Exception):
    def __init__(self, path, msg):
        self.path = path
        self.msg = msg

    def __str__(self):
        return ('Error parsing tool requirements from {!r}: {}'
                .format(self.path, self.msg))


class ToolReq:
    # A subclass can set this to configure the command that's run to get the
    # version of a tool. If tool_cmd is None, get_version will call "self.tool
    # --version".
    tool_cmd = None

    # Used by get_version. If not None, this is a dictionary that's added to
    # the environment when running the command.
    tool_env = None

    # A subclass can set this to configure _parse_version_output. If set, it
    # should be a Regex object with a single capturing group that captures the
    # version.
    version_regex = None

    def __init__(self, tool, min_version):
        self.tool = tool
        self.min_version = min_version
        self.optional = False

    def _get_tool_cmd(self):
        '''Return the command to run to get the installed version'''
        return self.tool_cmd or [self.tool, '--version']

    def _get_version(self):
        '''Run the tool to get the installed version.

        Raises a RuntimeError on failure. The default version uses the class
        variable tool_cmd to figure out what to run.

        '''

    def _parse_version_output(self, stdout):
        '''Parse the nonempty stdout to get a version number

        Raises a ValueError on failure. The default implementation returns the
        last word of the first line if version_regex is None or the first match
        for version_regex if it is not None.

        '''
        if self.version_regex is None:
            line0 = stdout.split('\n', 1)[0]
            words = line0.rsplit(None, 1)
            if not words:
                raise ValueError('Empty first line.')

            return words[-1]

        for line in stdout.split('\n'):
            match = self.version_regex.match(line.rstrip())
            if match is not None:
                return match.group(1)
        raise ValueError('No line matched version regex.')

    def get_version(self):
        '''Run the tool to get a version.

        Returns a version string on success. Raises a RuntimeError on failure.
        The default version uses the class variable tool_cmd to figure out what
        to run.

        '''
        cmd = self._get_tool_cmd()
        cmd_txt = ' '.join(shlex.quote(w) for w in cmd)

        env = None
        if self.tool_env is not None:
            env = os.environ.copy()
            env.update(self.tool_env)

        try:
            proc = subprocess.run(cmd,
                                  check=True,
                                  stdout=subprocess.PIPE,
                                  universal_newlines=True,
                                  env=env)
        except (subprocess.CalledProcessError, FileNotFoundError) as err:
            env_msg = ('' if not self.tool_env else
                       ' (with environment overrides: {})'
                       .format(', '.join('{}={}'.format(k, v)
                                         for k, v in self.tool_env.items())))
            raise RuntimeError('Failed to run {!r}{} to check version: {}'
                               .format(cmd_txt, env_msg, err))

        if not proc.stdout:
            raise RuntimeError('No output from running {!r} to check version.'
                               .format(cmd_txt))

        try:
            return self._parse_version_output(proc.stdout)
        except ValueError as err:
            raise RuntimeError('Bad output from running {!r} '
                               'to check version: {}'
                               .format(cmd_txt, err))

    def to_semver(self, version, from_req):
        '''Convert a tool version to semantic versioning format

        If from_req is true, this version comes from the requirements file
        (rather than being reported from an installed application). That might
        mean stricter checking. If version is not a known format, raises a
        ValueError.

        '''
        return version

    def check(self):
        '''Get the installed version and check it matches the requirements

        Returns (is_good, msg). is_good is true if we matched the requirements
        and false otherwise. msg describes what happened (an error message on
        failure, or extra information on success).

        '''
        try:
            min_semver = self.to_semver(self.min_version, True)
        except ValueError as err:
            return (False,
                    'Failed to convert requirement to semantic version: {}'
                    .format(err))
        try:
            min_sv = StrictVersion(min_semver)
        except ValueError as err:
            return (False,
                    'Bad semver inferred from required version ({}): {}'
                    .format(min_semver, err))

        try:
            actual_version = self.get_version()
        except RuntimeError as err:
            return (False, str(err))

        try:
            actual_semver = self.to_semver(actual_version, False)
        except ValueError as err:
            return (False,
                    'Failed to convert installed to semantic version: {}'
                    .format(err))
        try:
            actual_sv = StrictVersion(actual_semver)
        except ValueError as err:
            return (False,
                    'Bad semver inferred from installed version ({}): {}'
                    .format(actual_semver, err))

        if actual_sv < min_sv:
            return (False,
                    'Installed version is too old: '
                    'found version {}, but need at least {}'
                    .format(actual_version, self.min_version))

        return (True,
                'Sufficiently recent version (found {}; needed {})'
                .format(actual_version, self.min_version))


class VerilatorToolReq(ToolReq):
    def get_version(self):
        try:
            # Note: "verilator" needs to be called through a shell and with all
            # arguments in a string, as it doesn't have a shebang, but instead
            # relies on perl magic to parse command line arguments.
            version_str = subprocess.run('verilator --version', shell=True,
                                         check=True, stdout=subprocess.PIPE,
                                         stderr=subprocess.STDOUT,
                                         universal_newlines=True)
        except subprocess.CalledProcessError as err:
            raise RuntimeError('Unable to call Verilator to check version: {}'
                               .format(err)) from None

        return version_str.stdout.split(' ')[1].strip()


class VeribleToolReq(ToolReq):
    tool_cmd = ['verible-verilog-lint', '--version']

    def to_semver(self, version, from_req):
        # Drop the hash suffix and convert into version string that
        # is compatible with StrictVersion in check_version below.
        # Example: v0.0-808-g1e17daa -> 0.0.808
        m = re.fullmatch(r'v([0-9]+)\.([0-9]+)-([0-9]+)-g[0-9a-f]+$', version)
        if m is None:
            raise ValueError("{} has invalid version string format."
                             .format(version))

        return '.'.join(m.group(1, 2, 3))


class VcsToolReq(ToolReq):
    tool_cmd = ['vcs', '-full64', '-ID']
    tool_env = {'VCS_ARCH_OVERRIDE': 'linux'}
    version_regex = re.compile(r'Compiler version = VCS [A-Z]-(.*)')

    def to_semver(self, version, from_req):
        # VCS has a rather strange numbering scheme, where the most general
        # versions look something like this:
        #
        #    Q-2020.03-SP1-2
        #
        # Our version_regex strips out the "Q" part (a "platform prefix")
        # already. A version always has the "2020.03" (year and month) part,
        # and may also have an -SP<n> and/or -<patch> suffix.
        #
        # Since StrictVersion expects a 3 digit versioning scheme, we multiply
        # any SP number by 100, which should work as long as the patch version
        # isn't greater than 99.
        #
        # Some VCS builds also report other cruft (like _Full64) after this
        # version number. If from_req is False, allow (and ignore) that too.
        regex = r'([0-9]+).([0-9]+)(?:-SP([0-9]+))?(?:-([0-9]+))?'
        if from_req:
            regex += '$'

        match = re.match(regex, version)
        if match is None:
            raise ValueError("{!r} is not a recognised VCS version string."
                             .format(version))
        major = match.group(1)
        minor = match.group(2)
        sp = int(match.group(3) or 0)
        patch = int(match.group(4) or 0)
        comb = str(sp * 100 + patch)
        return '{}.{}{}'.format(major, minor, comb)


class PyModuleToolReq(ToolReq):
    '''A tool in a Python module (its version can be found by running pip)'''
    version_regex = re.compile(r'Version: (.*)')

    def _get_tool_cmd(self):
        return ['pip3', 'show', self.tool]


def dict_to_tool_req(path, tool, raw):
    '''Parse a dict (as read from Python) as a ToolReq

    Required keys: version. Optional keys: as_needed.

    '''
    where = 'Dict for {} in __TOOL_REQUIREMENTS__'.format(tool)
    # We operate in place on the dictionary. Take a copy to avoid an
    # obnoxious API.
    raw = raw.copy()

    if 'min_version' not in raw:
        raise ReqErr(path,
                     '{} is missing required key: "min_version".'
                     .format(where))
    min_version = raw['min_version']
    if not isinstance(min_version, str):
        raise ReqErr(path,
                     '{} has min_version that is not a string.'
                     .format(where))
    del raw['min_version']

    as_needed = False
    if 'as_needed' in raw:
        as_needed = raw['as_needed']
        if not isinstance(as_needed, bool):
            raise ReqErr(path,
                         '{} has as_needed that is not a bool.'
                         .format(where))
        del raw['as_needed']

    if raw:
        raise ReqErr(path,
                     '{} has unexpected keys: {}.'
                     .format(where, ', '.join(raw.keys())))

    classes = {
        'edalize': PyModuleToolReq,
        'vcs': VcsToolReq,
        'verible': VeribleToolReq,
        'verilator': VerilatorToolReq
    }
    cls = classes.get(tool, ToolReq)

    ret = cls(tool, min_version)
    ret.as_needed = as_needed
    return ret


def read_tool_requirements(path=None):
    '''Read tool requirements from a Python file'''
    if path is None:
        path = get_tool_requirements_path()

    with open(path, 'r') as pyfile:
        globs = {}
        exec(pyfile.read(), globs)

        # We expect the exec call to have populated globs with a
        # __TOOL_REQUIREMENTS__ dictionary.
        raw = globs.get('__TOOL_REQUIREMENTS__')
        if raw is None:
            raise ReqErr(path,
                         'The Python file at did not define '
                         '__TOOL_REQUIREMENTS__.')

        # raw should be a dictionary (keyed by tool name)
        if not isinstance(raw, dict):
            raise ReqErr(path, '__TOOL_REQUIREMENTS__ is not a dict.')

        reqs = {}
        for tool, raw_val in raw.items():
            if not isinstance(tool, str):
                raise ReqErr(path,
                             'Invalid key in __TOOL_REQUIREMENTS__: {!r}'
                             .format(tool))

            if isinstance(raw_val, str):
                # Shorthand notation: value is just a string, which we
                # interpret as a minimum version
                raw_val = {'min_version': raw_val}

            if not isinstance(raw_val, dict):
                raise ReqErr(path,
                             'Value for {} in __TOOL_REQUIREMENTS__ '
                             'is not a string or dict.'.format(tool))

            reqs[tool] = dict_to_tool_req(path, tool, raw_val)

        return reqs


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('tool', nargs='*')
    args = parser.parse_args()

    # Get tool requirements
    try:
        tool_requirements = read_tool_requirements()
    except ReqErr as err:
        log.error(str(err))
        return 1

    pending_tools = set(args.tool)
    missing_tools = []
    for tool, req in tool_requirements.items():
        if req.as_needed and tool not in pending_tools:
            continue
        pending_tools.discard(tool)

        good, msg = req.check()
        if not good:
            log.error('Failed tool requirement for {}: {}'
                      .format(tool, msg))
            missing_tools.append(tool)
        else:
            log.info('Tool {} present: {}'
                     .format(tool, msg))

    all_good = True
    if missing_tools:
        log.error("Tool requirements not fulfilled. "
                  "Please update tools ({}) and retry."
                  .format(', '.join(missing_tools)))
        all_good = False

    if pending_tools:
        log.error("Some tools specified on command line don't appear in "
                  "tool requirements file: {}"
                  .format(', '.join(sorted(pending_tools))))
        all_good = False

    return 0 if all_good else 1


if __name__ == "__main__":
    sys.exit(main())
