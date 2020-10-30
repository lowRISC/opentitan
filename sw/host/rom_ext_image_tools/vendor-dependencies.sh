#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -e

if [ "$#" != "1" ]; then
    printf "\nIncorrect usage:\n" >&2
    printf "Usage: $(basename "$0") add|remove\n" >&2
    exit 1
fi

rm -rf vendored_dependencies

if [ "$1" == "add" ]; then
    mkdir vendored_dependencies

    # TODO - do we need any?
    VENDOR_FLAGS=

    # Captures stdout but not stderr, which is exactly what we need.
    VENDOR_CMD_OUTPUT="$(cargo vendor vendored_dependencies $VENDOR_FLAGS)"
    echo "$VENDOR_CMD_OUTPUT"

    # Delete vendoring information from config.
    sed -i '/ROM_EXT_SIGNER_VENDORED_DEPENDENCIES_SETUP/q' .cargo/config.toml

    # Add vendoring information to the config.
    CONFIG="$(awk '/ROM_EXT_SIGNER_VENDORED_DEPENDENCIES_SETUP/{print; print a; next} 1' \
      a="$VENDOR_CMD_OUTPUT"                                                             \
      .cargo/config.toml)"

    # Commit the new config.
    echo "$CONFIG" > .cargo/config.toml

    echo ""
    echo "Config has been successfully updated!"
elif [ "$1" == "remove" ]; then
    # Delete vendoring information from config.
    sed -i '/ROM_EXT_SIGNER_VENDORED_DEPENDENCIES_SETUP/q' .cargo/config.toml
else
    printf "\nIncorrect usage:\n" >&2
    printf "Usage: $(basename "$0") add|remove\n" >&2
    exit 1
fi


