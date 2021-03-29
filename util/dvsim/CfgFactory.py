# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import logging as log
import sys

from CfgJson import load_hjson

import FormalCfg
import LintCfg
import SimCfg
import SynCfg


def _load_cfg(path, initial_values):
    '''Worker function for make_cfg.

    initial_values is passed to load_hjson (see documentation there).

    Returns a pair (cls, hjson_data) on success or raises a RuntimeError on
    failure.

    '''
    # Start by loading up the hjson file and any included files
    hjson_data = load_hjson(path, initial_values)

    # Look up the value of flow in the loaded data. This is a required field,
    # and tells us what sort of FlowCfg to make.
    flow = hjson_data.get('flow')
    if flow is None:
        raise RuntimeError('{!r}: No value for the "flow" key. Are you sure '
                           'this is a dvsim configuration file?'
                           .format(path))

    classes = [
        LintCfg.LintCfg,
        SynCfg.SynCfg,
        FormalCfg.FormalCfg,
        SimCfg.SimCfg
    ]
    found_cls = None
    known_types = []
    for cls in classes:
        assert cls.flow is not None
        known_types.append(cls.flow)
        if cls.flow == flow:
            found_cls = cls
            break
    if found_cls is None:
        raise RuntimeError('{}: Configuration file sets "flow" to {!r}, but '
                           'this is not a known flow (known: {}).'
                           .format(path, flow, ', '.join(known_types)))

    return (found_cls, hjson_data)


def _make_child_cfg(path, args, initial_values):
    try:
        cls, hjson_data = _load_cfg(path, initial_values)
    except RuntimeError as err:
        log.error(str(err))
        sys.exit(1)

    # Since this is a child configuration (from some primary configuration),
    # make sure that we aren't ourselves a primary configuration. We don't need
    # multi-level hierarchies and this avoids circular dependencies.
    if 'use_cfgs' in hjson_data:
        raise RuntimeError('{}: Configuration file has use_cfgs, but is '
                           'itself included from another configuration.'
                           .format(path))

    # Call cls as a constructor. Note that we pass None as the mk_config
    # argument: this is not supposed to load anything else.
    return cls(path, hjson_data, args, None)


def make_cfg(path, args, proj_root):
    '''Make a flow config by loading the config file at path

    args is the arguments passed to the dvsim.py tool and proj_root is the top
    of the project.

    '''
    initial_values = {'proj_root': proj_root}
    if args.tool is not None:
        initial_values['tool'] = args.tool

    try:
        cls, hjson_data = _load_cfg(path, initial_values)
    except RuntimeError as err:
        log.error(str(err))
        sys.exit(1)

    def factory(child_path):
        child_ivs = initial_values.copy()
        child_ivs['flow'] = hjson_data['flow']
        return _make_child_cfg(child_path, args, child_ivs)

    return cls(path, hjson_data, args, factory)
