# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# shellcheck shell=bash
#
# Shared helpers for the categorized lint runner (ci/lint/run.sh).
#
# This file is meant to be sourced, not executed. It deliberately does *not*
# set -e: the runner keeps going after a failing check so that a single job
# reports every problem in its category, then exits non-zero at the end via
# `lint_report`.

# Move to the repository root so every check has a stable working directory,
# whether the runner was invoked directly or through `nix run .#lint` (which
# runs from the caller's $PWD).
REPO_TOP="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"
cd "$REPO_TOP" || exit 1

# Target branch used by diff-based checks. Overridable; defaults to master.
OT_BASE_REF="${OT_BASE_REF:-master}"

# Whether to run checks that only make sense against a PR base (commit
# metadata, changed-file diffs). Enabled by default so local runs are
# thorough; CI disables it for non-pull-request events.
OT_RUN_PR_CHECKS="${OT_RUN_PR_CHECKS:-1}"

_ot_failures=()

# ot_merge_base: print the fork point against OT_BASE_REF, or nothing if it
# can't be determined (e.g. a shallow checkout with no remote-tracking ref) or
# if HEAD is itself the fork point. The latter is the push-to-master case: the
# merge base is HEAD, so a diff against it is empty and every changed-file check
# would report success without examining anything. Callers treat empty as "no
# base" and fall back to the whole tree, which is what makes a master push the
# place where drift in the whole-tree checks actually surfaces.
ot_merge_base() {
    local base
    base="$(git merge-base "origin/$OT_BASE_REF" HEAD 2>/dev/null ||
        git merge-base "$OT_BASE_REF" HEAD 2>/dev/null ||
        true)"
    [ "$base" = "$(git rev-parse HEAD 2>/dev/null)" ] && return 0
    printf '%s' "$base"
}

# section <description>: print a header, collapsible under GitHub Actions.
section() {
    if [ -n "${GITHUB_ACTIONS:-}" ]; then
        echo "::group::$1"
    else
        printf '\n\033[1m### %s\033[0m\n' "$1"
    fi
}

_ot_endsection() {
    [ -n "${GITHUB_ACTIONS:-}" ] && echo "::endgroup::"
    return 0
}

# check <description> <cmd...>: run a blocking check, recording failure but
# continuing so every check in the category gets a chance to report.
check() {
    local desc="$1"
    shift
    section "$desc"
    if "$@"; then
        _ot_endsection
    else
        _ot_endsection
        echo "::error::lint check failed: ${desc}" >&2
        _ot_failures+=("$desc")
    fi
}

# soft_check <description> <cmd...>: non-blocking variant that Warns but never fails.
soft_check() {
    local desc="$1"
    shift
    section "$desc (non-blocking)"
    "$@" || echo "::warning::non-blocking lint check failed: ${desc}" >&2
    _ot_endsection
}

# pr_check <description> <cmd...>: a blocking check that only runs in PR
# context (skipped when OT_RUN_PR_CHECKS != 1).
pr_check() {
    local desc="$1"
    shift
    if [ "$OT_RUN_PR_CHECKS" != "1" ]; then
        section "$desc (skipped: not a pull request)"
        _ot_endsection
        return 0
    fi
    check "$desc" "$@"
}

# lint_report: exit non-zero if any blocking check failed.
lint_report() {
    if [ "${#_ot_failures[@]}" -ne 0 ]; then
        echo >&2
        echo "::error::${#_ot_failures[@]} lint check(s) failed:" >&2
        printf '  - %s\n' "${_ot_failures[@]}" >&2
        exit 1
    fi
    echo
    echo "All lint checks passed."
}
