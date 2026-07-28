#!/usr/bin/env bash
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Categorized lint runner: the single source of truth for the lint flow, used
# both locally (via `nix run .#lint`) and by CI (one category per job).
#
# Usage:
#   ci/lint/run.sh                 # run every category (all tops)
#   ci/lint/run.sh <category>...   # run the named categories
#   ci/lint/run.sh hw <top>        # run hardware lint for a single top
#
# Categories:
#   hygiene   text/metadata/python hygiene checks     (Nix tools)
#   gen       generated & vendored file freshness     (Nix tools)
#   hw        per-top Verible + countermeasure lint   (Nix tools)
#   sv        whole-tree Verible sweep, advisory only (Nix tools)
#   bazel     Bazel-graph hygiene + link/alert checks (requires Bazel)
#
# Every category runs from the tools provided by the `lint` devShell, so
# `nix run .#lint` reproduces them exactly. The `bazel` category shells out to
# ./bazelisk.sh, which picks up the devShell's Bazel from PATH (its version
# matches .bazelversion) instead of downloading bazelisk; in CI it also needs
# the remote cache credentials from prepare-env.

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=ci/lint/lib.sh
source "$SCRIPT_DIR/lib.sh"

# All tops the project builds. The per-top `hw` category figures out which
# checks actually apply to each (see cat_hw).
ALL_TOPS=(earlgrey darjeeling englishbreakfast)

# ---------------------------------------------------------------------------
# hygiene: fast text, metadata and Python checks. No Bazel, no hardware.
# (Bazel-backed checks such as licence headers and lock files live in the
# `bazel` category, which is the group set up with a working Bazel toolchain.)
# ---------------------------------------------------------------------------
# _changed_or_all <git-pathspec>...: print files changed since the merge base,
# or all tracked matching files when no merge base is available (which includes
# a push to master, where the merge base is HEAD; see ot_merge_base).
#
# `--diff-filter=d` drops deletions: the callers hand this list to linters, which
# fail on a path that no longer exists on disk. (The scripts under ci/scripts
# filter the same way, spelling it `--diff-filter=ACMRTUXB`.) Renames are
# reported under their new name, so they still get checked.
_changed_or_all() {
    local base
    base="$(ot_merge_base)"
    if [ -n "$base" ]; then
        git diff --name-only --diff-filter=d "$base" -- "$@"
    else
        git ls-files -- "$@"
    fi
}

# ruff is scoped to files changed since the merge base (matching the old flake8
# step and limiting a from-scratch run to the current change).
#
# --config picks the gating rule set in ci/lint/ruff-ci.toml over the one in
# pyproject.toml. The latter is aimed at editors and deliberately turns on
# ruff's preview rules, which is a moving target: the set grows with each ruff
# release, so enforcing it would make a dependency bump fail the lint on
# untouched code. See that file for the rule list and how to extend it.
_lint_ruff() {
    local files
    mapfile -t files < <(_changed_or_all '*.py' ':!*/vendor/*')
    if [ "${#files[@]}" -eq 0 ]; then echo "No Python files to check."; return 0; fi
    echo "Checking ${#files[@]} Python file(s) with ruff."
    ruff check --config ci/lint/ruff-ci.toml "${files[@]}"
}

cat_hygiene() {
    check    "Environment info"          ci/scripts/show-env.sh
    pr_check "Commit metadata"           ci/scripts/lint-commits.sh "$OT_BASE_REF"
    check    "Executable bits"           ci/scripts/exec-check.sh
    check    "Non-ASCII characters"      ci/scripts/check-ascii.sh
    pr_check "Python lint (flake8)"      ci/scripts/python-lint.sh "$OT_BASE_REF"
    check    "Python typecheck (mypy)"   ci/scripts/mypy.sh
    check    "Python lint (ruff)"        _lint_ruff
    check    "Testplan schema"           ci/scripts/validate_testplans.sh
    pr_check "Header guards"             ci/scripts/include-guard.sh "$OT_BASE_REF"
    pr_check "Trailing whitespace"       ci/scripts/whitespace.sh "$OT_BASE_REF"
    check    "ASM instrumentation"       util/coverage/asm/run_instrument.sh --check
    check    "Generated command blocks"  ci/scripts/check-cmdgen.sh
}

# ---------------------------------------------------------------------------
# gen: generated and vendored files must be clean and up to date.
# ---------------------------------------------------------------------------
cat_gen() {
    # check-generated regenerates files in place, then restores the tree with
    # `git clean -fxd && git reset --hard` (only when OT_DESTRUCTIVE=1). That
    # deletes ALL uncommitted changes *and* gitignored files (.venv, build
    # outputs, scratch/, .bazelrc-site), so it is only safe in a throwaway CI
    # checkout. Its own docs say: "Never set OT_DESTRUCTIVE=1 automatically,
    # except to define the CI environment." Honour that: run it destructively
    # in CI only. Locally, skip it so a stray `nix run .#lint` can never wipe a
    # developer's working tree.
    if [ -n "${GITHUB_ACTIONS:-}" ]; then
        check "Generated files" env OT_DESTRUCTIVE=1 ci/scripts/check-generated.sh
    else
        section "Generated files (skipped locally: OT_DESTRUCTIVE resets the tree)"
        echo "Skipped: check-generated runs 'git clean -fxd && git reset --hard'," >&2
        echo "which deletes uncommitted changes and gitignored files. To run it" >&2
        echo "against a disposable tree yourself:" >&2
        echo "    OT_DESTRUCTIVE=1 ci/scripts/check-generated.sh" >&2
        _ot_endsection
    fi
    check "Vendored files"  ci/scripts/check-vendoring.sh
}

# ---------------------------------------------------------------------------
# hw <top>: per-top hardware lint. Only the checks that apply to the given
# top are run, so the same entrypoint works for every matrix leg.
#
# This lints exactly what the per-top lint cfgs pull in: the set that carries
# correctly scoped waivers (fusesoc supplies the per-core context) and can
# therefore gate. Files no cfg reaches are linted advisorily by `sv` below.
# ---------------------------------------------------------------------------
cat_hw() {
    local top="$1"
    if [ -z "$top" ]; then
        echo "::error::the 'hw' category requires a top name" >&2
        exit 2
    fi
    # Without this an unknown top just matches no lint cfgs and no
    # countermeasure case, so a typo would run nothing and report success.
    if ! printf '%s\n' "${ALL_TOPS[@]}" | grep -qxF "$top"; then
        echo "::error::unknown top: $top" >&2
        echo "Valid tops: ${ALL_TOPS[*]}" >&2
        exit 2
    fi

    # Verible style lint (design/DV/FPV). Run for whichever flavours the top
    # actually provides a lint config for.
    #
    # englishbreakfast is skipped: although it ships lint cfgs, they have
    # bit-rotted (never having been exercised by CI, which only ever linted
    # earlgrey and darjeeling) and no longer resolve. top_englishbreakfast_
    # lint_cfgs.hjson names fusesoc cores that do not exist, e.g.
    # lowrisc:englishbreakfast_ip:otp_ctrl -- englishbreakfast has no
    # ip_autogen/otp_ctrl -- so fusesoc errors out before any linting happens.
    # Fixing those cfgs is a separate, hardware-side change; until then this
    # keeps the coverage CI has today rather than adding a permanently red
    # check. Countermeasures for this top are checked below, as before.
    local flavour cfg
    for flavour in rtl dv fpv; do
        [ "$top" = "englishbreakfast" ] && continue
        case "$flavour" in
            rtl) cfg="hw/top_${top}/lint/top_${top}_lint_cfgs.hjson" ;;
            dv)  cfg="hw/top_${top}/lint/top_${top}_dv_lint_cfgs.hjson" ;;
            fpv) cfg="hw/top_${top}/lint/top_${top}_fpv_lint_cfgs.hjson" ;;
        esac
        if [ -f "$cfg" ]; then
            check "Verible ${flavour} (${top})" ci/scripts/verible-lint.sh "$flavour" "$top"
        fi
    done

    # Countermeasures are only checked for the tops that support it today.
    case "$top" in
        earlgrey|englishbreakfast)
            check "Countermeasures (${top})" ci/scripts/check-countermeasures.sh "$top"
            ;;
    esac
}

# ---------------------------------------------------------------------------
# bazel: checks that query or build the Bazel graph. These require a working
# Bazel setup (./bazelisk.sh) and so are *not* provided by the lint devShell.
# ---------------------------------------------------------------------------
cat_bazel() {
    # Formatting (C/C++, Rust, Starlark) and shellcheck, run from the tools
    # //quality pins: the RISC-V toolchain's clang-format, rules_rust's rustfmt,
    # buildifier_prebuilt and @shellcheck. Keeping them on the pinned binaries
    # means these checks and the documented `bazel run //quality:format` fix path
    # cannot disagree; a nixpkgs copy of each would be faster and diff-scopable,
    # but formatter output is version-sensitive and nothing in CI would notice
    # the two drifting apart. Both targets are whole-tree: rules_lint's
    # format_test has no notion of a merge base.
    check      "Formatting, shellcheck"  ./bazelisk.sh test \
        //quality:format_check //quality:shellcheck_check
    pr_check   "Licence headers"         ci/scripts/check-licence-headers.sh "$OT_BASE_REF"
    check      "Lock files"              ci/scripts/check-lock-files.sh
    check      "Banned Bazel rules"      ci/scripts/check-bazel-banned-rules.sh
    check      "Bazel target names"      ci/scripts/check_bazel_target_names.py
    soft_check "Bazel test suite tags"   ci/scripts/check_bazel_test_suites.py
    soft_check "DV software images"      ci/scripts/check_dv_sw_images.sh
    check      "Broken links"            ci/scripts/check-links.sh
    check "Alert classification (earlgrey)" \
        ci/scripts/validate_alert_classification.py \
        hw/top_earlgrey/ip_autogen/alert_handler/data/top_earlgrey_alert_handler.ipconfig.hjson \
        "$(realpath hw/top_earlgrey/data/otp/otp_ctrl_img_owner_sw_cfg.hjson)"
    check "Alert classification (darjeeling)" \
        ci/scripts/validate_alert_classification.py \
        hw/top_darjeeling/ip_autogen/alert_handler/data/top_darjeeling_alert_handler.ipconfig.hjson \
        "$(realpath hw/top_darjeeling/data/otp/otp_ctrl_img_owner_sw_cfg.hjson)"
}

# ---------------------------------------------------------------------------
# Dispatch
# ---------------------------------------------------------------------------
ALL_CATEGORIES=(hygiene gen hw bazel)

# _is_category <word>: true if <word> names a lint category.
_is_category() {
    local c
    for c in "${ALL_CATEGORIES[@]}"; do [ "$1" = "$c" ] && return 0; done
    return 1
}

run_category() {
    case "$1" in
        hygiene) cat_hygiene ;;
        gen)     cat_gen ;;
        bazel)   cat_bazel ;;
        hw)
            if [ -n "${2:-}" ]; then
                cat_hw "$2"
            else
                for top in "${ALL_TOPS[@]}"; do cat_hw "$top"; done
            fi
            ;;
        *)
            echo "::error::unknown lint category: $1" >&2
            echo "Valid categories: ${ALL_CATEGORIES[*]}" >&2
            exit 2
            ;;
    esac
}

main() {
    if [ "$#" -eq 0 ]; then
        # No arguments: run everything.
        cat_hygiene
        cat_gen
        for top in "${ALL_TOPS[@]}"; do cat_hw "$top"; done
        cat_bazel
    elif [ "$#" -eq 2 ] && [ "$1" = hw ] && ! _is_category "$2"; then
        # The parameterised form `hw <top>`: the second word is an argument to
        # the category, not another category. Requiring that it not name a
        # category keeps `run.sh hw gen` reading as two categories, which is
        # the only sense it can have.
        run_category "$1" "$2"
    else
        # Otherwise every argument is a category, run in the order given.
        local category
        for category in "$@"; do run_category "$category"; done
    fi
    lint_report
}

main "$@"
