#!/usr/bin/env python3

# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import collections
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

    if not isinstance(config_dict, collections.Mapping):
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


def _config_dict_to_fusesoc_opts(config_dict):
    fusesoc_cmd = []
    for parameter, value in config_dict.items():
        if isinstance(value, bool):
            # For fusesoc boolean parameter are set to true if given on the
            # command line otherwise false, it doesn't support an explicit
            # --param=True style
            if value:
                fusesoc_cmd.append(shlex.quote('--' + parameter))
        else:
            fusesoc_cmd.append(shlex.quote('--' + parameter + '=' + str(value)))

    return ' '.join(fusesoc_cmd)


def get_config_file_location():
    """Returns the location of the config file

    Default is _DEFAULT_CONFIG_FILE and the IBEX_CONFIG_FILE environment
    variable overrides the default"""

    return os.environ.get('IBEX_CONFIG_FILE', _DEFAULT_CONFIG_FILE)


def main():
    config_outputs = {'fusesoc_opts': _config_dict_to_fusesoc_opts}

    argparser = argparse.ArgumentParser(description=(
        'Outputs Ibex configuration '
        'parameters for a named config in a number of formats.  If not '
        'specified on the command line the config will be read from {0}. This '
        'default can be overridden by setting the IBEX_CONFIG_FILE environment '
        'variable').format(get_config_file_location()))

    argparser.add_argument('config_name',
                           help=('The name of the Ibex '
                                 'configuration to output'))

    argparser.add_argument('output_type',
                           help=('Format to output the '
                                 'configuration parameters in'),
                           choices=config_outputs.keys())

    argparser.add_argument('--config_filename',
                           help='Config file to read',
                           default=get_config_file_location())

    args = argparser.parse_args()

    try:
        config_file = open(args.config_filename)
        config_dicts = get_config_dicts(config_file)

        if args.config_name not in config_dicts:
            print('ERROR: configuration',
                  args.config_name,
                  'not found in',
                  args.config_filename,
                  file=sys.stderr)

            sys.exit(1)

        print(config_outputs[args.output_type](config_dicts[args.config_name]))
    except ConfigException as ce:
        print('ERROR: failure to read configuration from',
              args.config_filename,
              ce,
              file=sys.stderr)
        sys.exit(1)
    except FileNotFoundError:
        print('ERROR: could not find configuration file',
              args.config_filename,
              file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
