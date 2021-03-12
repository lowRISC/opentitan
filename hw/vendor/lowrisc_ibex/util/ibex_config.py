#!/usr/bin/env python3

# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import collections.abc
import os
import shlex
import sys

import yaml

_DEFAULT_CONFIG_FILE = 'ibex_configs.yaml'


class ConfigException(Exception):
    pass


def _verify_config(name, config_dict):
    """Checks a config_dict matches expectations.

    A config_dict is the dictionary mapping parameters to values for a
    particular config, it must obey the following rules:
        - It's a mapping object e.g. OrderedDict
        - Its values can only be strings, integers or booleans

    Args:
        name: The name of the config being checked (used to form useful error
        messages)
        config_dict: The config_dict to check, must be a mapping object

    Returns:
        Nothing, an exception is thrown if an issue is found

    Raises:
        ConfigException: An issue was found with config_dict
    """

    if not isinstance(config_dict, collections.abc.Mapping):
        raise ConfigException('Config ' + name +
                              ' must have dictionary giving parameters')

    for k, v in config_dict.items():
        if isinstance(v, int):
            continue
        if isinstance(v, str):
            continue
        if isinstance(v, bool):
            continue

        raise ConfigException('Parameter ' + k + ' for config ' + name +
                              ' must be string, int or bool got ' +
                              str(type(v)))


def _verify_config_parameters(config_dicts):
    """Verifies all parameters across config_dicts match expectations.

    Each configuration must obey the following fules:
        - Each config has the same set of parameters specified

    Args:
        config_dicts: A dictionary of configurations, maps from configuration
        name to a configuration (itself a dictionary)

    Returns:
        Nothing, an exception is thrown if an issue is found

    Raises:
        ConfigException: An issue was found with config_dicts
    """

    parameters = set()

    first = True

    for name, config_dict in config_dicts.items():
        parameters_this_config = set()

        for parameter, value in config_dict.items():
            if first:
                parameters.add(parameter)

            parameters_this_config.add(parameter)

        if first:
            first = False
        else:
            parameter_difference = parameters ^ parameters_this_config
            if parameter_difference:
                raise ConfigException('Config ' + name +
                                      ' has differing parameters ' +
                                      ','.join(parameter_difference))


def get_config_dicts(config_file):
    """Extracts a dictionary of configuration dictionaries from a file object

    Given a file object parses YAML from it to obtain a dictionary of
    configurations

    Args:
        config_file: A file object for a file containing the YAML configuration
        file

    Returns:
        A dictionary of configurations, maps from a configuration name to a
        configuration (itself a dictionary mapping parameters to values)

    Raises:
        ConfigException: An issue was found with the configuration file
    """

    try:
        config_yaml = yaml.load(config_file, Loader=yaml.SafeLoader)
    except yaml.YAMLError as e:
        raise ConfigException('Could not decode yaml:\n' + str(e))

    for k, v in config_yaml.items():
        _verify_config(k, v)

    _verify_config_parameters(config_yaml)

    return config_yaml


class FusesocOpts:
    def setup_args(self, arg_subparser):
        output_argparser = arg_subparser.add_parser(
            'fusesoc_opts', help=('Outputs options for fusesoc'))
        output_argparser.set_defaults(output_fn=self.output)

    def output(self, config_dict, args):
        fusesoc_cmd = []
        for parameter, value in config_dict.items():
            if isinstance(value, bool):
                # For fusesoc boolean parameters are set to true if given on the
                # command line otherwise false. It doesn't support an explicit
                # --param=True style
                if value:
                    fusesoc_cmd.append(shlex.quote('--' + parameter))
            else:
                fusesoc_cmd.append(
                    shlex.quote('--' + parameter + '=' + str(value)))

        return ' '.join(fusesoc_cmd)


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

    def output(self, config_dict, args):
        if (args.ins_hier_path != ''):
            ins_hier_path = args.ins_hier_path + self.hierarchy_sep
        else:
            ins_hier_path = ''

        sim_opts = []

        for parameter, value in config_dict.items():
            if isinstance(value, str):
                parameter_define = args.string_define_prefix + parameter
                define_set_str = self.define_set_fn(parameter_define, value)

                if define_set_str:
                    sim_opts.append(shlex.quote(define_set_str))
            else:
                if isinstance(value, bool):
                    val_str = '1' if value else '0'
                else:
                    val_str = str(value)

                param_set_str = self.param_set_fn(ins_hier_path + parameter,
                                                  val_str)

                if param_set_str:
                    sim_opts.append(shlex.quote(param_set_str))

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

    Returns: the chosen Ibex config as a YAML object.

    Raises a ConfigException if there are any error while parsing the YAML.

    Raises a FileNotFoundError if there are errors opening the chosen config file.
    """
    try:
        config_file = open(config_filename)
        config_dicts = get_config_dicts(config_file)

        if config_name not in config_dicts:
            print('ERROR: configuration {!r} not found in {!r}.'.format(
                  config_name, config_filename), file=sys.stderr)
            sys.exit(1)
        return config_dicts[config_name]
    except ConfigException as ce:
        print('ERROR: failure to process configuration from {!r} {!r}.'.format(
              config_filename, ce), file=sys.stderr)
        sys.exit(1)
    except FileNotFoundError:
        print('ERROR: could not find configuration file {!r}.'.format(
              config_filename), file=sys.stderr)
        sys.exit(1)


def main():
    outputters = [
        FusesocOpts(),
        SimOpts('vcs_opts', 'VCS compile',
                lambda p, v: '-pvalue+' + p + '=' + v,
                lambda d, v: '+define+' + d + '=' + v, '.'),
        SimOpts('riviera_sim_opts', 'Riviera simulate',
                lambda p, v: '-g/' + p + '=' + v,
                lambda d, v: None, '/'),
        SimOpts('riviera_compile_opts', 'Riviera compile',
                lambda p, v: None,
                lambda d, v: '+define+' + d + '=' + v, '/'),
        SimOpts('questa_sim_opts', 'Questa simulate',
                lambda p, v: '-g/' + p + '=' + v,
                lambda d, v: None, '/'),
        SimOpts('questa_compile_opts', 'Questa compile',
                lambda p, v: None,
                lambda d, v: '+define+' + d + '=' + v, '/'),
        SimOpts('xlm_opts', 'Xcelium compile',
                lambda p, v: '-defparam ' + p + '=' + v,
                lambda d, v: '-define ' + d + '=' + v, '.'),
        SimOpts('dsim_compile_opts', 'DSim compile',
                lambda p, v: '+define+' + p + '=' + v,
                lambda d, v: None, '/'),
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
