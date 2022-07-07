#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Map the "dev" user to an UID passed in as environment variable to ensure
# files are written by the same UID/GID into mounted volumes.
DEV_UID=${DEV_UID:-1000}
DEV_GID=${DEV_GID:-1000}
groupmod -o -g "$DEV_GID" dev >/dev/null 2>&1
usermod -o -u "$DEV_UID" dev >/dev/null 2>&1

# Load user configuration.
test -f "${USER_CONFIG}" && export BASH_ENV=${USER_CONFIG}

cd /home/dev || exit
exec gosu dev:dev /bin/bash -c "$@"
