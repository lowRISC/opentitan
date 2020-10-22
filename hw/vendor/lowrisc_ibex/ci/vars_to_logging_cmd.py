#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Read an Azure Pipelines-compatible variables file, and convert it into
# logging commands that Azure Pipelines understands, effectively setting the
# variables at runtime.
#
# This script can be used as a workaround if variables cannot be included in the
# Pipeline definition directly.
#
# See https://docs.microsoft.com/en-us/azure/devops/pipelines/scripts/logging-commands
# for more information on logging commands.

import sys
import yaml

def vars_to_logging_cmd(vars_file):
    data = {}
    print(vars_file)
    with open(vars_file, 'r', encoding="utf-8") as fp:
        data = yaml.load(fp, Loader=yaml.SafeLoader)

    if not (isinstance(data, dict) and 'variables' in data):
        print("YAML file wasn't a dictionary with a 'variables' key. Got: {}"
            .format(data))

    print("Setting variables from {}".format(vars_file))
    for key, value in data['variables'].items():
        # Note: These lines won't show up in the Azure Pipelines output unless
        # "System Diagnostics" are enabled (go to the Azure Pipelines web UI,
        # click on "Run pipeline" to manually run a pipeline, and check "Enable
        # system diagnostics".)
        print("##vso[task.setvariable variable={}]{}".format(key, value))

    return 0

if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: {} VARS_FILE".format(sys.argv[0]))
        sys.exit(1)
    sys.exit(vars_to_logging_cmd(sys.argv[1]))
