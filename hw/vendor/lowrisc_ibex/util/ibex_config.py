#!/usr/bin/env python3

# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import os
import shlex
import sys

import yaml

_DEFAULT_CONFIG_FILE = 'ibex_configs.yaml'


class ConfigException(Exception):
    pass


class Config:
    '''An object representing an Ibex configuration'''
    known_fields = [
        ('RV32E', bool),
        ('RV32M', str),
        ('RV32B', str),
        ('RegFile', str),
        ('BranchTargetALU', bool),
        ('WritebackStage', bool),
        ('ICache', bool),
        ('ICacheECC', bool),
        ('ICacheScramble', bool),
        ('BranchPredictor', bool),
        ('DbgTriggerEn', bool),
        ('SecureIbex', bool),
        ('PMPEnable', bool),
        ('PMPGranularity', int),
        ('PMPNumRegions', int),
        ('MHPMCounterNum', int),
        ('MHPMCounterWidth', int)
    ]

    def __init__(self, yml):
        if not isinstance(yml, dict):
            raise ValueError('Configuration object is not a dict')

        yaml_keys = set(yml.keys())
        known_keys = {fld for (fld, typ) in Config.known_fields}

        extra_keys = yaml_keys - known_keys
        if extra_keys:
            raise ValueError(f'Configuration object has '
                             f'unknown keys: {extra_keys}')

        missing_keys = known_keys - yaml_keys
        if missing_keys:
            raise ValueError(f'Configuration object has '
                             f'missing keys: {extra_keys}')

        self.params = yml

        self.rv32e = Config.read_bool('RV32E', yml)
        self.rv32m = Config.read_str('RV32M', yml)
        self.rv32b = Config.read_str('RV32B', yml)
        self.reg_file = Config.read_str('RegFile', yml)
        self.branch_target_alu = Config.read_bool('BranchTargetALU', yml)
        self.writeback_stage = Config.read_bool('WritebackStage', yml)
        self.icache = Config.read_bool('ICache', yml)
        self.icache_ecc = Config.read_bool('ICacheECC', yml)
        self.icache_scramble = Config.read_bool('ICacheScramble', yml)
        self.branch_predictor = Config.read_bool('BranchPredictor', yml)
        self.dbg_trigger_en = Config.read_bool('DbgTriggerEn', yml)
        self.secure_ibex = Config.read_bool('SecureIbex', yml)
        self.pmp_enable = Config.read_bool('PMPEnable', yml)
        self.pmp_granularity = Config.read_int('PMPGranularity', yml)
        self.pmp_num_regions = Config.read_int('PMPNumRegions', yml)
        self.mhpm_counter_num = Config.read_int('MHPMCounterNum', yml)
        self.mhpm_counter_width = Config.read_int('MHPMCounterWidth', yml)

    @staticmethod
    def read_bool(fld, yml):
        val = yml[fld]
        if isinstance(val, bool):
            return val
        if isinstance(val, int):
            if 0 <= val <= 1:
                return val != 0

            raise ValueError(f'{fld} value is {val}, which is out of '
                             'range for a boolean type.')
        raise ValueError(f'{fld} value is {val!r}, but we expected a bool.')

    @staticmethod
    def read_int(fld, yml):
        val = yml[fld]
        if isinstance(val, int):
            return val
        raise ValueError(f'{fld} value is {val!r}, but we expected an int.')

    @staticmethod
    def read_str(fld, yml):
        val = yml[fld]
        if isinstance(val, str):
            return val
        raise ValueError(f'{fld} value is {val!r}, but we expected a string.')


class Configs:
    def __init__(self, yml):
        if not isinstance(yml, dict):
            raise ValueError('Configurations dictionary is not a dict')

        self.configs = {}
        for cfg_name, cfg_yaml in yml.items():
            try:
                self.configs[cfg_name] = Config(cfg_yaml)
            except ValueError as err:
                raise ValueError(f'Error when reading '
                                 f'{cfg_name!r} config: {err}') from None


class FusesocOpts:
    def setup_args(self, arg_subparser):
        output_argparser = arg_subparser.add_parser(
            'fusesoc_opts', help=('Outputs options for fusesoc'))
        output_argparser.set_defaults(output_fn=self.output)

    def output(self, config, args):
        fusesoc_cmd = []
        for fld, typ in Config.known_fields:
            val = config.params[fld]
            fusesoc_cmd.append(shlex.quote(f'--{fld}={val}'))

        return ' '.join(fusesoc_cmd)

class QueryOpts:
    def setup_args(self, arg_subparser):
        output_argparser = arg_subparser.add_parser(
            'query_fields', help=('Query config fields'))
        output_argparser.add_argument(
            'fields', type=str, nargs='+',
            help='Which fields to query the value of')

        output_argparser.set_defaults(output_fn=self.output)

    def output(self, config, args):
        query_result = []
        for fld in args.fields:
            if fld in config.params:
                val = config.params[fld]
                query_result.append(f'{fld}={val}')
            else:
                query_result.append(f'{fld} not found in config')

        return '\n'.join(query_result)

class SimOpts:
    def __init__(self, cmd_name, description, param_set_fn, define_set_fn,
                 hierarchy_sep):
        self.cmd_name = cmd_name
        self.description = description
        self.param_set_fn = param_set_fn
        self.define_set_fn = define_set_fn
        self.hierarchy_sep = hierarchy_sep

    def setup_args(self, arg_subparser):
        output_argparser = arg_subparser.add_parser(
            self.cmd_name,
            help=('Outputs options for {0}'.format(self.description)))

        output_argparser.add_argument(
            '--ins_hier_path',
            help=('Hierarchical path to the instance to set '
                  'configuration parameters on'),
            default='')
        output_argparser.add_argument(
            '--string_define_prefix',
            help=('Prefix to add to defines that are used to '
                  'pass string parameters'),
            default='')
        output_argparser.set_defaults(output_fn=self.output)

    def output(self, config, args):
        if (args.ins_hier_path != ''):
            ins_hier_path = args.ins_hier_path + self.hierarchy_sep
        else:
            ins_hier_path = ''

        sim_opts = []

        for fld, typ in Config.known_fields:
            val = config.params[fld]

            if typ is str:
                parameter_define = args.string_define_prefix + fld
                define_opts = self.define_set_fn(parameter_define, val)
                sim_opts += [shlex.quote(arg) for arg in define_opts]
            else:
                assert typ in [bool, int]

                # Explicitly convert to 0/1 (handling genuine booleans)
                val_as_int = int(val)

                full_param = ins_hier_path + fld
                param_opts = self.param_set_fn(full_param, str(val_as_int))
                sim_opts += [shlex.quote(arg) for arg in param_opts]

        return ' '.join(sim_opts)


def get_config_file_location():
    """Returns the location of the config file

    Default is _DEFAULT_CONFIG_FILE and the IBEX_CONFIG_FILE environment
    variable overrides the default"""

    return os.environ.get('IBEX_CONFIG_FILE', _DEFAULT_CONFIG_FILE)


def parse_config(config_name, config_filename):
    """Parses the selected config file and returns selected config information.

    Arguments:

        config_name: Name of the chosen Ibex core config

        config_filename: Name of the configuration filename to be parsed

    Returns: the chosen Ibex config as a Config object.

    Raises an exception if there is an error loading or parsing the YAML, or if
    the YAML doesn't define a configuration with the requested name.

    """
    with open(config_filename) as config_file:
        try:
            yml = yaml.load(config_file, Loader=yaml.SafeLoader)
        except yaml.YAMLError as err:
            raise ConfigException(f'Could not decode yaml: {err}')

    try:
        configs = Configs(yml)
    except ValueError as err:
        raise ConfigException(f'{config_filename!r}: {err}') from None

    config = configs.configs.get(config_name)
    if config is None:
        raise ValueError(f'Configuration {config_name!r} not found '
                         'in YAML at {config_filename!r}.')

    return config


def main():
    outputters = [
        FusesocOpts(),
        QueryOpts(),
        SimOpts('vcs_opts', 'VCS compile',
                lambda p, v: ['-pvalue+' + p + '=' + v],
                lambda d, v: ['+define+' + d + '=' + v], '.'),
        SimOpts('riviera_sim_opts', 'Riviera simulate',
                lambda p, v: ['-g/' + p + '=' + v],
                lambda d, v: [], '/'),
        SimOpts('riviera_compile_opts', 'Riviera compile',
                lambda p, v: [],
                lambda d, v: ['+define+' + d + '=' + v], '/'),
        SimOpts('questa_sim_opts', 'Questa simulate',
                lambda p, v: ['-g/' + p + '=' + v],
                lambda d, v: [], '/'),
        SimOpts('questa_compile_opts', 'Questa compile',
                lambda p, v: [],
                lambda d, v: ['+define+' + d + '=' + v], '/'),
        SimOpts('xlm_opts', 'Xcelium compile',
                lambda p, v: ['-defparam',  p + '=' + v],
                lambda d, v: ['-define', d + '=' + v], '.'),
        SimOpts('dsim_compile_opts', 'DSim compile',
                lambda p, v: ['+define+' + p + '=' + v],
                lambda d, v: [], '/'),
    ]

    argparser = argparse.ArgumentParser(description=(
        'Outputs Ibex configuration parameters for a named config in a number '
        'of formats.  If not specified on the command line the config will be '
        'read from {0}. This default can be overridden by setting the '
        'IBEX_CONFIG_FILE environment variable. Some output types support '
        'arguments to see help for them pass a config_name and an output type '
        'followed by --help').format(get_config_file_location()))

    argparser.add_argument('config_name',
                           help=('The name of the Ibex '
                                 'configuration to output'))

    argparser.add_argument('--config_filename',
                           help='Config file to read',
                           default=get_config_file_location())

    arg_subparser = argparser.add_subparsers(
        help='Format to output the configuration parameters in',
        dest='output_fn',
        metavar='output_type')

    for outputter in outputters:
        outputter.setup_args(arg_subparser)

    args = argparser.parse_args()

    if args.output_fn is None:
        print('ERROR: No output format specified.')
        sys.exit(1)

    parsed_ibex_config = parse_config(args.config_name, args.config_filename)
    print(args.output_fn(parsed_ibex_config, args))

if __name__ == "__main__":
    main()
