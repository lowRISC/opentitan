#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Returns 0 if there are no changes or untracked files, 1 otherwise.
# Show the diff on STDOUT if there's deviation.
is_clean() {
    local output
    output="$(git status --porcelain)" || return 1
    test -z "$output" && return 0
    echo Diff between the regenerated content and the content in this PR/the repository:
    git diff
    return 1
}

# Clean up the repo so that we can check further auto-generated stuff
cleanup() {
    git clean -fxd >/dev/null
    git reset --hard >/dev/null
}

# Run a command and then check the tree is still clean. Print a message if not.
gen_and_check_clean() {
    thing="$1"
    shift
    "$@" || {
        echo -n "##vso[task.logissue type=error]"
        echo "Failed to auto-generate $thing. (command: '$*')"
        echo
        cleanup
        return 1
    }

    is_clean || {
        echo -n "##vso[task.logissue type=error]"
        echo "Auto-generated $thing not up-to-date. Regenerate with '$*'."
        echo
        cleanup
        return 1
    }
}

# A specialized version of gen_and_check_clean for targets of the Makefile in hw
gen_hw_and_check_clean() {
    gen_and_check_clean "$1" make -k -C hw "$2"
}

# Check generated files are up to date

bad=0
cleanup

gen_hw_and_check_clean "Register headers" regs         || bad=1
gen_hw_and_check_clean "tops"             top          || bad=1
gen_hw_and_check_clean "OTP memory map"   otp-mmap     || bad=1
gen_hw_and_check_clean "LC state"         lc-state-enc || bad=1

gen_and_check_clean \
    "flash_ctrl code" \
    hw/ip/flash_ctrl/util/flash_ctrl_gen.py || bad=1

gen_and_check_clean \
    "secded primitive code" \
    util/design/secded_gen.py --no_fpv || bad=1

gen_and_check_clean \
    "DIFs" \
    util/make_new_dif.py --mode=regen --only=autogen || bad=1

gen_and_check_clean "MUBI package" util/design/gen-mubi.py || bad=1

exit $bad
