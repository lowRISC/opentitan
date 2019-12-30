#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""
Utility functions common across dvsim.
"""

import logging as log
import os
import pprint
import re
import shlex
import subprocess
import sys
import time
from collections import OrderedDict

import hjson

# For verbose logging
VERBOSE = 15


# Run a command and get the result. Exit with error if the command did not
# succeed. This is a simpler version of the run_cmd function below.
def run_cmd(cmd):
    (status, output) = subprocess.getstatusoutput(cmd)
    if status:
        sys.stderr.write("cmd " + cmd + " returned with status " + str(status))
        sys.exit(status)
    return output


# Run a command with a specified timeout. If the command does not finish before
# the timeout, then it returns -1. Else it returns the command output. If the
# command fails, it throws an exception and returns the stderr.
def run_cmd_with_timeout(cmd, timeout=-1, exit_on_failure=1):
    args = shlex.split(cmd)
    p = subprocess.Popen(args,
                         stdout=subprocess.PIPE,
                         stderr=subprocess.STDOUT)

    # If timeout is set, poll for the process to finish until timeout
    result = ""
    status = -1
    if timeout == -1:
        p.wait()
    else:
        start = time.time()
        while time.time() - start < timeout:
            if p.poll() is not None:
                break
            time.sleep(0.2)

    # Capture output and status if cmd exited, else kill it
    if p.poll() is not None:
        result = p.communicate()[0]
        status = p.returncode
    else:
        log.error("cmd \"%s\" timed out!", cmd)
        p.kill()

    if status != 0:
        log.error("cmd \"%s\" exited with status %d", cmd, status)
        if exit_on_failure == 1: sys.exit(status)

    return (result, status)


def subst_wildcards(var, mdict, ignored_wildcards=[]):
    '''
    If var has wildcards specified within {..}, find and substitute them.
    '''
    def subst(wildcard, mdict):
        if wildcard in mdict.keys(): return mdict[wildcard]
        else: return None

    if "{eval_cmd}" in var:
        idx = var.find("{eval_cmd}") + 11
        var = subst_wildcards(var[idx:], mdict, ignored_wildcards)
        var = run_cmd(var)
    else:
        match = re.findall(r"{([A-Za-z0-9\_]+)}", var)
        if len(match) > 0:
            subst_list = {}
            for item in match:
                if item not in ignored_wildcards:
                    log.debug("Found wildcard in \"%s\": \"%s\"", var, item)
                    found = subst(item, mdict)
                    if found is not None:
                        if type(found) is str:
                            found = subst_wildcards(found, mdict,
                                                    ignored_wildcards)
                        if type(found) is bool:
                            found = int(found)
                        subst_list[item] = found
                    else:
                        # Check if the wildcard exists as an environment variable
                        env_var = os.environ.get(item)
                        if env_var is not None: subst_list[item] = env_var
                        else:
                            log.error(
                                "Substitution for the wildcard \"%s\" not found",
                                item)
                            sys.exit(1)
            for item in subst_list:
                var = var.replace("{" + item + "}", str(subst_list[item]))
    return var


def find_and_substitute_wildcards(sub_dict, full_dict, ignored_wildcards=[]):
    '''
    Recursively find key values containing wildcards in sub_dict in full_dict
    and return resolved sub_dict.
    '''
    for key in sub_dict.keys():
        if type(sub_dict[key]) in [dict, OrderedDict]:
            # Recursively call this funciton in sub-dicts
            sub_dict[key] = find_and_substitute_wildcards(
                sub_dict[key], full_dict, ignored_wildcards)

        elif type(sub_dict[key]) is list:
            sub_dict_key_values = list(sub_dict[key])
            # Loop through the list of key's values and substitute each var
            # in case it contains a wildcard
            for i in range(len(sub_dict_key_values)):
                if type(sub_dict_key_values[i]) in [dict, OrderedDict]:
                    # Recursively call this funciton in sub-dicts
                    sub_dict_key_values[i] = \
                        find_and_substitute_wildcards(sub_dict_key_values[i],
                                                      full_dict, ignored_wildcards)

                elif type(sub_dict_key_values[i]) is str:
                    sub_dict_key_values[i] = subst_wildcards(
                        sub_dict_key_values[i], full_dict, ignored_wildcards)

            # Set the substituted key values back
            sub_dict[key] = sub_dict_key_values

        elif type(sub_dict[key]) is str:
            sub_dict[key] = subst_wildcards(sub_dict[key], full_dict,
                                            ignored_wildcards)

    return sub_dict
