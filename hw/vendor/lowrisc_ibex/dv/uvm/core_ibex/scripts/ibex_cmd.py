# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import subprocess
from typing import Tuple, Dict, List
from typeguard import typechecked

from setup_imports import _IBEX_ROOT
import ibex_config
from ibex_config import Config, parse_config

import logging
logger = logging.getLogger(__name__)

# For each simulator, a tuple
#
#    (needs_compile_opts, needs_sim_opts)
#
SIM_CFGS = {
    'vcs': (True, False),
    'riviera': (True, True),
    'questa': (True, True),
    'xlm': (True, False),
    'dsim': (True, False)
}


class GenError(Exception):
    pass


def _run_ibex_config(config_name: str, output_type: str) -> str:
    script_path = _IBEX_ROOT/'util'/'ibex_config.py'
    yaml_path = _IBEX_ROOT/'ibex_configs.yaml'

    ibex_config_cmd = [
        str(script_path),
        '--config_filename', str(yaml_path),
        config_name,
        output_type,
        '--ins_hier_path', 'core_ibex_tb_top',
        '--string_define_prefix', 'IBEX_CFG_'
    ]
    proc = subprocess.run(ibex_config_cmd,
                          stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE,
                          universal_newlines=True)

    if proc.returncode != 0:
        raise GenError("Error running {0} got:\n{1}\n{2}"
                       .format(script_path, proc.stdout, proc.stderr))

    return proc.stdout.strip()


def _get_x_opts(config_name: str, simulator: str, stage: str) -> str:
    try:
        needs_compile_opts, needs_sim_opts = SIM_CFGS[simulator]
    except KeyError:
        raise ValueError(f'Unsupported simulator: {simulator}.')

    specify_which_opts = needs_compile_opts and needs_sim_opts

    if stage == 'compile':
        needs_opts = needs_compile_opts
    elif stage == 'sim':
        needs_opts = needs_sim_opts
    else:
        assert 0

    if not needs_opts:
        return ''

    output_type = (f'{simulator}_{stage}_opts'
                   if specify_which_opts else f'{simulator}_opts')

    return _run_ibex_config(config_name, output_type)


def get_compile_opts(config_name: str, simulator: str) -> str:
    return _get_x_opts(config_name, simulator, 'compile')


def get_sim_opts(config_name: str, simulator: str) -> str:
    return _get_x_opts(config_name, simulator, 'sim')


def get_config(cfg_name: str) -> Config:
    yaml_path = _IBEX_ROOT/"ibex_configs.yaml"
    return parse_config(cfg_name, yaml_path)


def get_isas_for_config(cfg: Config) -> Tuple[str, str]:
    """Get ISA and ISS_ISA keys for the given Ibex config."""
    # NOTE: This logic should match the code in the get_isa_string() function
    # in core_ibex/tests/core_ibex_base_test.sv: keep them in sync!
    has_multiplier = cfg.rv32m != 'ibex_pkg::RV32MNone'
    base_isa = 'rv32{}{}c'.format('e' if cfg.rv32e else 'i',
                                  'm' if has_multiplier else '')

    bitmanip_mapping = {
        'ibex_pkg::RV32BNone': [],
        'ibex_pkg::RV32BBalanced': ['Zba', 'Zbb', 'Zbs', 'XZbf', 'XZbt'],
        'ibex_pkg::RV32BOTEarlGrey': ['Zba', 'Zbb', 'Zbc', 'Zbs',
                                      'XZbf', 'XZbp', 'XZbr', 'XZbt'],
        'ibex_pkg::RV32BFull': ['Zba', 'Zbb', 'Zbc', 'Zbs',
                                'XZbe', 'XZbf', 'XZbp', 'XZbr', 'XZbt']
    }

    bitmanip_isa = bitmanip_mapping.get(cfg.rv32b)
    if bitmanip_isa is None:
        raise ValueError(f'Unknown RV32B value ({cfg.rv32b}) in config YAML')

    has_bitmanip = cfg.rv32b != 'ibex_pkg::RV32BNone'
    toolchain_isa = base_isa + ('b' if has_bitmanip else '')

    return (toolchain_isa, '_'.join([base_isa] + bitmanip_isa))


_TestEntry = Dict[str, object]
_TestEntries = List[_TestEntry]


@typechecked
def filter_tests_by_config(cfg: ibex_config.Config,
                           test_list: _TestEntries) -> _TestEntries:
    """Filter out any unsupported tests from being executed.

    e.g. if the "small" config has been specified, this function will filter
    out all tests that require B-extension and PMP parameters

    This function will parse the set of RTL parameters required by a given
    test (if any) and ensure that those parameters are supported by the
    selected core config.

    Doing this allows the run flow to be smarter about running regressions
    with different configs (useful for CI flows).

    Arguments:
        cfg: ibex_config.Config object of built system
        test_list: list of test entry objects parsed from the YAML testlist

    Returns:
        filtered_test_list: a list of test entry objects, filtered such that
                            all tests incompatible with the specified ibex
                            config have been removed.
    """
    filtered_test_list = []

    for test in test_list:
        if "rtl_params" not in test:
            # We currently only exclude tests by mismatching 'rtl_params', so if
            # that key is missing then the test is accepted by default.
            filtered_test_list.append(test)
        else:
            param_dict = test['rtl_params']
            assert isinstance(param_dict, dict)
            for p, p_val in param_dict.items():
                config_val = cfg.params.get(p, None)

                # Throw an error if required RTL parameters in the testlist
                # have been formatted incorrectly (typos, wrong parameters,
                # etc)
                if config_val is None:
                    raise ValueError('Parameter {} not found in config {}'
                                     .format(p, cfg))

                # Ibex has some enum parameters, so as a result some tests are
                # able to run with several of these parameter values (like
                # bitmanipulation tests). If this is the case, the testlist
                # will specify all legal enum values, check if any of them
                # match the config.
                if ((isinstance(p_val, list) and (config_val not in p_val)) or
                    (isinstance(p_val, str)  and (config_val != p_val))):
                    logger.warning(
                        f"Rejecting test {test['test']}, 'rtl_params' specified "
                        "not compatible with ibex_config")
                    break

                # The test is accepted if we got this far
                filtered_test_list.append(test)

    return filtered_test_list
