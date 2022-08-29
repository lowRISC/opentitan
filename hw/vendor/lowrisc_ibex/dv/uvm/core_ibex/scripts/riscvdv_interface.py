"""Defines the interface to riscvdv features for random instruction generation and compilation.

riscv-dv provides both
- a runnable instruction-generator
  (the sv/UVM program that actually generates .S assembly files)

- formatting guidelines for specifying simulators, test commands, optional arguments, etc.
  (testlist.yaml / simulator.yaml)

Provide an interface to get runnable commands from data/configuration specified in
the riscdv way.
"""

# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import re
import shlex
import pathlib3x as pathlib
from typing import Union, List, Dict
from typeguard import typechecked

from metadata import RegressionMetadata

# ibex
from setup_imports import _RISCV_DV, _CORE_IBEX_RISCV_DV_EXTENSION
from scripts_lib import subst_dict, subst_env_vars

# riscv-dv
from lib import read_yaml

import logging
logger = logging.getLogger(__name__)

parameter_format = '<{}>'
parameter_regex = r'(<[\w]+>)'  # Find matches to the above format


@typechecked
def get_run_cmd(verbose: bool) -> List[Union[str, pathlib.Path]]:
    """Return the command parts of a call to riscv-dv's run.py."""
    riscvdv_run_py = _RISCV_DV/'run.py'
    csr_desc = _CORE_IBEX_RISCV_DV_EXTENSION/'csr_description.yaml'
    testlist = _CORE_IBEX_RISCV_DV_EXTENSION/'testlist.yaml'

    cmd = ['python3',
           riscvdv_run_py,
           '--testlist', testlist,
           '--gcc_opts=-mno-strict-align',
           '--custom_target', _CORE_IBEX_RISCV_DV_EXTENSION,
           # '--simulator_yaml', _CORE_IBEX_YAML/'rtl_simulation.yaml',
           '--csr_yaml', csr_desc,
           '--mabi=ilp32']
    if verbose:
        cmd.append('--verbose')

    return cmd


def get_cov_cmd(md: RegressionMetadata) -> List[str]:
    """Return the the command to generate riscv-dv's functional coverage."""
    riscvdv_cov_py = _RISCV_DV/'cov.py'

    cmd = ['python3',
           str(riscvdv_cov_py),
           '--core', 'ibex',
           '--dir', str(md.dir_run),
           '-o', str(md.dir_fcov),
           '--simulator', md.simulator,
           '--opts', '--gen_timeout 1000',
           '--isa', md.isa_ibex,
           '--custom_target', str(md.ibex_riscvdv_customtarget)]
    if md.verbose:
        cmd.append('--verbose')

    return cmd


@typechecked
def get_tool_cmds(yaml_path: pathlib.Path,
                  simulator: str,
                  cmd_type: str, # compile/sim
                  user_enables: Dict[str, bool],
                  user_subst_options: Dict[str, Union[str, pathlib.Path]]) -> List[List[str]]:
    """Substitute options and environment variables to construct a final command.

    simulator is the name of the simulator to use.
    cmd_type is Union['compile','sim']
    user_subst_opts is a dict[str, str] of templated variables <T> in the
    yaml commands that are to be substituted as <T> = user_subst_opts[T]

    RISCV_DV allows both compile and sim keys in the yaml to have
    multiple commands, so return [str]

    Populate the riscv-dv rtl_simulation.yaml templated parameters <T> with
    the following algorithm...

    (1) If the yaml key 'tool':'compile/sim' contains K:V pairs with keys other
        than 'cmd', for each of those keys K check if <K> exists in the cmd, and
        if it does, substitute for the value V. Gate each substitution with a
        user-specified enable.
    (2) For any remaining templated values <_> in the cmd, take a user-defined
        dict {K:V} and if <K> matches the templated value, replace <K> by V.
    (3) If the yaml key 'tool' set contains a K:V pair 'env_var':[str],
        then for each str in [str], check if it exists as a templated value <V>
        in the cmd, and if it does, substitute with the environment variable of
        the same name.

    enable_dict should be a dict mapping names to bools.
    For each key, N, in enable_dict, if enable_dict[N] is False, then all
    occurrences of <N> in cmd will be replaced with ''.
    If enable_dict[N] is True, all occurrences of <N> in cmd will be replaced
    with opts_dict[N].

    If N is not a key in opts_dict, this is no problem unless cmd contains
    <N>, in which case we throw a RuntimeError.

    Finally, the environment variables are substituted as described in
    subst_env_vars and any newlines are stripped out.

    """
    simulator_entry = _get_yaml_for_simulator(yaml_path, simulator)
    cmds = []

    for cmd in simulator_entry[cmd_type]['cmd']:
        assert type(cmd) == str
        formatted_cmd = cmd
        logger.debug("Unformatted command :")
        logger.debug(formatted_cmd)

        # (1) #
        # Get all k:v pairs which are not 'cmd'
        # Substitute with matching parameters in the command, or if the
        # parameter is disabled by a user_enable, remove it.
        cmd_opts_dict = {k: (v.strip() if user_enables.get(k) else '')
                         for k, v in simulator_entry[cmd_type].items()
                         if k != 'cmd'}
        if cmd_opts_dict != {}:
            formatted_cmd = subst_dict(formatted_cmd, cmd_opts_dict)
        logger.debug("After #1 :")
        logger.debug(formatted_cmd)

        # (2) #
        if user_subst_options != {}:
            formatted_cmd = subst_dict(formatted_cmd, user_subst_options)
        logger.debug("After #2 :")
        logger.debug(formatted_cmd)

        # (3) #
        if 'env_var' in simulator_entry.keys():
            formatted_cmd = subst_env_vars(
                formatted_cmd,
                [i for i in simulator_entry['env_var'].replace(' ', '').split(',')]
            )
        logger.debug("After #3 :")
        logger.debug(formatted_cmd)

        # Finally, check if we have any parameters left which were not filled.
        match = re.findall(parameter_regex, formatted_cmd)
        if match:
            logger.error("Parameters in riscvdv command not substituted!\n"
                        f"Parameters : {match}\n"
                        f"Command :  {formatted_cmd}\n")
            raise RuntimeError

        logger.info(formatted_cmd)
        cmds.append(shlex.split(formatted_cmd))

    return cmds


@typechecked
def _get_yaml_for_simulator(yaml_path: pathlib.Path, simulator: str) -> dict:
    """Get the entry for the simulator in RTL simulation yaml.

    riscv-dv specifies a yaml-schema for defining simulators and commands needed
    for building and running testbenches.
    The ibex build system uses this schema  with it's own unique commands, in
    the file 'rtl_simulation.yaml'.
    Trigger an exception if there is no match.
    """
    logger.info("Processing simulator setup file : %s" % yaml_path)
    for entry in read_yaml(yaml_path):
        if entry.get('tool') == simulator:
            logger.debug(f"Got the following yaml for simulator '{simulator}' "
                         f"from {str(yaml_path.resolve())} :\n{entry}")
            return entry

    raise RuntimeError("Cannot find RTL simulator {}".format(simulator))
