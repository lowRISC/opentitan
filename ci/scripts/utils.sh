#!/bin/bash
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Bash utilities intended to be sourced by and used within CI.

# Retry a command a few times, to work around transient failures.
# Uses an exponential back-off scheme to avoid re-trying too soon.
# See https://github.com/rust-lang/rust/blob/5a30e4307f0506bed87eeecd171f8366fdbda1dc/src/ci/shared.sh#L12
#  Param 1 is the maximum number of attempts.
#  Param 2 is the initial time to sleep in seconds on failure.
#  Param 3 is the multiplicative backoff factor (an integer).
# e.g. retry 5 2 2 echo test message
retry () {
    local max_attempts="$1"
    local sleep_time="$2"
    local backoff_factor="$3"
    shift 3
    echo "Attempting with retry (attempt 1/$max_attempts):" "$@"
    local attempt=1
    while true; do
        "$@" && err=0 && break || err=$? && {
            if [[ $attempt -lt $max_attempts ]]; then
                echo "Command failed. Sleeping for $sleep_time seconds..."
                sleep "$sleep_time"
                sleep_time=$(( sleep_time * backoff_factor ))
                ((attempt++))
                echo "Retrying (attempt $attempt/$max_attempts):"
            else
                echo "Command failed after $attempt attempts."
                if [[ "$err" -ne 0 ]]; then
                    return "$err"
                else
                    return 1
                fi
            fi
        }
    done
}
