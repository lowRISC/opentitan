# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import logging as log
import os
import sys

from LocalLauncher import LocalLauncher
from LsfLauncher import LsfLauncher
from Scheduler import Scheduler

try:
    from EdaCloudLauncher import EdaCloudLauncher
    EDACLOUD_LAUNCHER_EXISTS = True
except ImportError:
    EDACLOUD_LAUNCHER_EXISTS = False

# The chosen launcher type.
launcher_type = None


def set_launcher_type(is_local=False):
    '''Sets the launcher type that will be used to launch the jobs.

    The env variable `DVSIM_LAUNCHER` is used to identify what launcher system
    to use. This variable is specific to the user's work site. It is meant to
    be set externally before invoking DVSim. Valid values are [local, lsf,
    edacloud]. If --local arg is supplied then the local launcher takes
    precedence.
    '''

    launcher = os.environ.get("DVSIM_LAUNCHER", "local")
    if is_local:
        launcher = "local"

    global launcher_type
    if launcher == "local":
        launcher_type = LocalLauncher

    elif launcher == "lsf":
        launcher_type = LsfLauncher

        # The max_parallel setting is not relevant when dispatching with LSF.
        Scheduler.max_parallel = sys.maxsize

    # These custom launchers are site specific. They may not be committed to the
    # open source repo.
    elif launcher == "edacloud" and EDACLOUD_LAUNCHER_EXISTS:
        launcher_type = EdaCloudLauncher

    else:
        log.error("Launcher {} set using DVSIM_LAUNCHER env var does not "
                  "exist. Using local launcher instead.".format(launcher))
        launcher_type = LocalLauncher


def get_launcher(deploy):
    '''Returns an instance of a launcher.

    'deploy' is an instance of the deploy class to with the launcher is paired.
    '''

    global launcher_type
    assert launcher_type is not None
    return launcher_type(deploy)
