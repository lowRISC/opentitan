#!/usr/bin/env bash
#
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Helper script that reads a file from stdin and replaces every tab character
# with at most eight spaces (i.e. what smart tabs would render it as at an
# eight-space tab.
# 
# This is useful for cleaning up the output of GCC tools that are excited about
# mixing tabs and spaces.

set -e

# A simple perl program that matches every tab in every line
# and replaces it with `8 - n % 8` spaces, where `n` is the
# index of the tab. Although the array $@ holds this
# information, it does not account for previous tab
# replacements, so we need to maintain a running total of
# how many new spaces we've added, which we do with `$acc`.
perl -pe '
    my $acc = 0;
    s/\t/
        my $sp = 8 - ($acc + $-[0]) % 8;
        $acc += $sp - 1;
        " " x $sp
    /eg'