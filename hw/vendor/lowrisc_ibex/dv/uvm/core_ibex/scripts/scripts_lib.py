#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import os
import shlex
import subprocess
import sys
import pickle
import pathlib3x as pathlib
from io import IOBase
from typing import Dict, TextIO, Optional, Union, List
from typing_utils import get_args
import dataclasses
from typeguard import typechecked


import logging
logger = logging.getLogger(__name__)


@typechecked
def run_one(verbose: bool,
            cmd: List[str],
            redirect_stdstreams: Optional[Union[str, pathlib.Path, IOBase]] = None,
            timeout_s: Optional[int] = None,
            reraise: bool = False,
            env: Dict[str, str] = None) -> int:
    """Run a command, returning its retcode.

    If verbose is true, print the command to stderr first (a bit like bash -x).

    The cmd argument must be formatted the idiomatic pythonic way, as list[str].

    If redirect_stdstreams is true, redirect the stdout and stderr of the
    subprocess to the given file object or path. Be flexible here to different
    possible destinations.
    """
    stdstream_dest = None
    needs_closing = False

    if redirect_stdstreams is not None:
        if redirect_stdstreams == '/dev/null':
            stdstream_dest = subprocess.DEVNULL
        elif isinstance(redirect_stdstreams, pathlib.Path):
            stdstream_dest = open(redirect_stdstreams, 'wb')
            needs_closing = True
        elif isinstance(redirect_stdstreams, IOBase):
            stdstream_dest = redirect_stdstreams
        else:
            raise RuntimeError(
                f"redirect_stdstream called as {redirect_stdstreams} "
                f"but that argument is invalid.")

    cmd_str = ' '.join(shlex.quote(w) for w in cmd)
    if verbose:
        # The equivalent of bash -x
        if redirect_stdstreams is not None:
            if isinstance(redirect_stdstreams, str):
                redir = f'>{shlex.quote(redirect_stdstreams)}'
            else:
                redir = f'>>{shlex.quote(redirect_stdstreams.name)}'
            cmd_str = f'{cmd_str} {redir} 2>&1'

        print('+ ' + cmd_str, file=sys.stderr)

        # Try to print the command to the file as well. This will fail if it's
        # a binary file: ignore the failure.
        if stdstream_dest:
            try:
                print('+ ' + cmd_str, file=stdstream_dest)
            except (TypeError, AttributeError):
                pass

    try:
        # Passing close_fds=False ensures that if cmd is a call to Make then
        # we'll pass through the jobserver fds. If you don't do this, you get a
        # warning starting "warning: jobserver unavailable".
        ps = subprocess.run(cmd,
                            stdout=stdstream_dest,
                            stderr=stdstream_dest,
                            close_fds=False,
                            timeout=timeout_s,
                            env=env)
        return ps.returncode
    except subprocess.CalledProcessError:
        print(ps.communicate()[0])
        return(1)
    except OSError as e:
        print(e)
        # print(ps.communicate()[0])
        return(1)
    except subprocess.TimeoutExpired as e:
        print("Error: Timeout[{}s]: {}".format(timeout_s, cmd_str))
        if reraise:
            raise e
        else:
            return(1)
    finally:
        if needs_closing:
            stdstream_dest.close()


@typechecked
def format_to_cmd(input_arg: Union[str, List[any]]) -> List[str]:
    """Format useful compound-lists into list[str], suitable for subprocess.

    Can be a list of [str, int, bool, pathlib.Path]
    """
    cmd_list = []
    for item in input_arg:
        try:
            cmd_list.append(format_to_str(item))
        except TypeError as e:
            raise RuntimeError(f"Can't format item to str when constructing a cmd: {e}")

    return cmd_list


@typechecked
def subst_opt(string: str, name: str, replacement: str) -> str:
    """Substitute the <name> option in string with 'replacement'."""
    from riscvdv_interface import parameter_format
    needle = parameter_format.format(name)
    if needle in string:
        logger.debug(f"Substituting <{name}> with {replacement}")
        return string.replace(needle, replacement)
    else:
        logger.debug(f"Tried to substitute for <{name}> in cmd but it was not found.")
        return string


@typechecked
def subst_dict(string: str, var_dict: Dict[str, Union[str, pathlib.Path]]) -> str:
    """Apply substitutions in var_dict to string.

    If <K> in string, substitute <K> for var_dict[K].
    """
    for key, value in var_dict.items():
        if isinstance(value, pathlib.Path):
            # Resolve to absolute path
            string = subst_opt(string, key, str(value.resolve()))
        else:
            string = subst_opt(string, key, value)
    return string


@typechecked
def subst_env_vars(string: str, env_vars: List[str]) -> str:
    """Substitute environment variables in string.

    For each environment variable, V, in the list, any
    occurrence of <V> in string will be replaced by the value of the
    environment variable with that name. If <V> occurs in the string but $V is
    not set in the environment, an error is raised.

    """
    for var in env_vars:
        value = os.environ.get(var)
        if value is None:
            raise RuntimeError('Cannot substitute {} in command because '
                               'the environment variable ${} is not set.'
                               .format(var, var))
        string = subst_opt(string, var, value)

    return string


# If any of these characters are present in a string output it in multi-line
# mode. This will either be because the string contains newlines or other
# characters that would otherwise need escaping
_YAML_MULTILINE_CHARS = ['[', ']', ':', "'", '"', '\n']
_YAML_PRINTABLE_TYPES = Union[int, str, bool]


@typechecked
def _yaml_value_format(val: _YAML_PRINTABLE_TYPES) -> str:
    """Format a value for yaml output.

    For int, str and bool value can just be converted to str with special
    handling for some strings
    """
    # If val is a multi-line string
    if isinstance(val, str) and any(c in val for c in _YAML_MULTILINE_CHARS):
        # Split into individual lines and output them after a suitable yaml
        # multi-line string indicator ('|-') indenting each line.
        lines = val.split('\n')
        return '|-\n' + '\n'.join([f'  {line}' for line in lines])

    if val is None:
        return ''

    return str(val)


@typechecked
def pprint_dict(d: dict, output: TextIO) -> None:
    """Pretty-Print a python dictionary as valid yaml.

    Align all the values to the same offset.
    eg.
    spam      eggs
    turkey    gravy
    yorkshire pudding
    """
    klen = 1
    for k in d.keys():
        klen = max(klen, len(k))

    for k, v in d.items():
        kpad = ' ' * (klen - len(k))
        output.write(f'{k}:{kpad} {_yaml_value_format(v)}\n')


@typechecked
def format_dict_to_printable_dict(arg: dict) -> dict:
    """Convert all dictionary keys to strings."""
    clean_dict = {}
    for k, v in arg.items():
        try:
            if isinstance(v, dict):
                clean_dict[k] = str(v)
                continue
            elif isinstance(v, list):
                clean_dict[k] = ' '.join([format_to_str(item)
                                         for item in v])
            else:
                clean_dict[k] = format_to_str(v)
        except TypeError:
            clean_dict[k] = str(v)  # see what happens? yolo
            pass

    return clean_dict


def format_to_str(arg: any) -> str:
    """Format single arg to str or raise exception if unable."""
    if isinstance(arg, get_args(_YAML_PRINTABLE_TYPES)):
        return str(arg)
    elif isinstance(arg, pathlib.Path):
        return str(arg.resolve())
    elif (arg is None):
        # Maybe remove?
        return ''
    else:
        raise TypeError("Couldn't format element to str!")


class testdata_cls():
    """Baseclass for testdata to hold common methods....

    Objects inheriting from this can easily import/export
    themselves to files, allowing data to gain continuinty between
    different phases of the regression and testing process
    """

    @classmethod
    @typechecked
    def construct_from_pickle(cls, metadata_pickle: pathlib.Path):
        """Allow easy contruction of the data-structure from a file."""
        trr = cls()
        logger.debug(f"Constructing object from data in {metadata_pickle}")
        with metadata_pickle.open('rb') as handle:
            trr = pickle.load(handle)
        return trr

    @typechecked
    def export(self, write_yaml: bool = False):
        """Write the object to disk.

        Simultaneously write a pickle file and a yaml-file
        for easy human consumption.

        This should only be called from contexts where there
        won't be races to write into the file. So, only
        export if you are sure only one process has opened
        the file. (eg. use LockedMetadata())
        """
        # TODO redesign to try and remove the above restriction
        # with better API design

        if not self.pickle_file:
            logger.error(f"Tried to export {type(self).__name__} but self.pickle_file has no path set!")
            raise RuntimeError
        if not self.yaml_file:
            logger.error(f"Tried to export {type(self).__name__} but self.yaml_file has no path set!")
            raise RuntimeError

        logger.info(f"Dumping object to {self.pickle_file}")
        self.pickle_file.parent.mkdir(parents=True, exist_ok=True)
        with self.pickle_file.open('wb') as handle:
            pickle.dump(self, handle)

        if not write_yaml:
            return

        self.yaml_file.parent.mkdir(parents=True, exist_ok=True)
        with self.yaml_file.open('w') as handle:
            pprint_dict(self.format_to_printable_dict(), handle)
            # TRIED EXPERIMENTING HERE BUT IT WASN'T SO PRETTY \"
            # pp = pprint.PrettyPrinter(indent=4, stream=handle)
            # pp.pprint(self.format_to_printable_dict())

    def format_to_printable_dict(self) -> dict:
        """Return a printable dict of the object with all-str fields.

        Recommended for human-consumption
        """
        return format_dict_to_printable_dict(dataclasses.asdict(self))
