# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_skylib//rules:common_settings.bzl", "BuildSettingInfo")
load("@lowrisc_opentitan//rules/opentitan:providers.bzl", "OpenTitanTestInfo")
load("@lowrisc_opentitan//rules:devices.bzl", "LIST_FPGA_SCRIPT")
load("@devices//:devices.bzl", "CW_DEVICES")

_TEST_SCRIPT = """
set -euo pipefail

expected='{CW_DEVICES}'

{LIST_FPGA_SCRIPT}

# Confirm ChipWhisperer devices are the same as when Bazel was invoked.
actual="$(list_fpga)"

if [[ "$actual" != "$expected" ]]; then
  echo "ERROR: Expected ChipWhisperer devices '$expected', but found '$actual'." >&2
  echo "This indicates the devices available on the host have changed since Bazel was invoked." >&2
  echo 'Please re-run `./bazelisk.sh fetch --repo=@devices --force`.' >&2
  echo "" >&2
  exit 1
fi

echo 'Test selected: {TEST_LABEL}'

{TEST}
"""

def check_fpga_availability(label):
    """Check if a specific FPGA is available for a test.

    Args:
      label: The label of the execution environment.
    Returns:
      bool: Whether the FPGA is available.
    """
    if "cw310" in label and "CW310" not in CW_DEVICES:
        return False
    if "hyper310" in label and "CW310" not in CW_DEVICES:
        return False
    if "cw340" in label and "CW340" not in CW_DEVICES:
        return False
    if "cw305" in label and "CW305" not in CW_DEVICES:
        return False
    return True

def test_pattern(label, pattern):
    """Checks if a label matches a preference pattern.

    Args:
      label: The execution environment label.
      pattern: The pattern to match (substring or suffix ending in $).
    Returns:
      bool: Whether the label matches the pattern.
    """
    if pattern.endswith("$"):
        return label.endswith(pattern[:-1])
    return pattern in label

def find_best_test_variant(tests, preference):
    """Finds the best test variant based on execution environment preference.

    Args:
        tests: A list of targets with OpenTitanTestInfo providers.
        preference: A list of patterns for exec_env labels, either a substring or a suffix ending with $.
    Returns:
        The target that matches the highest priority preference.
    """

    # Ensure the pattern only uses supported regex characters ($).
    for pattern in preference:
        for char in pattern.elems():
            if char in "[]{}()|.*?\\^":
                fail("Pattern {} has unsupported regex characters.".format(pattern))

    first_match = None
    tests = list(tests)
    for pattern in preference:
        for test in tests:
            info = test[OpenTitanTestInfo]
            label = str(info.exec_env.exec_env)
            if test_pattern(label, pattern):
                first_match = test
                if check_fpga_availability(label):
                    return test

    # If no available exec_env is found, return the first match to ensure the
    # Bazel build graph remains valid.
    return first_match

def _opentitan_select_test_impl(ctx):
    """Finds the best test variant based on execution environment preference.

    Args:
        ctx: The rule context.
    Returns:
        The target that matches the highest priority preference.
    """
    out = ctx.actions.declare_file(ctx.label.name)

    if len(ctx.attr.tests) == 0:
        ctx.actions.write(
            output = out,
            content = """
              echo "ERROR: No test targets found." >&2
              exit 1
            """,
            is_executable = True,
        )
        return [DefaultInfo(executable = out)]

    preference = ctx.attr._preference[BuildSettingInfo].value
    test = find_best_test_variant(ctx.attr.tests, preference)
    if not test:
        fail("No test in group matches the execution environment preference.")

    info = test[DefaultInfo]

    # Test wrapper that also checks for outdated device info.
    ctx.actions.write(
        output = out,
        content = _TEST_SCRIPT.format(
            CW_DEVICES = CW_DEVICES,
            LIST_FPGA_SCRIPT = LIST_FPGA_SCRIPT,
            TEST_LABEL = str(test.label),
            TEST = test[DefaultInfo].files_to_run.executable.short_path,
        ),
        is_executable = True,
    )

    return [
        DefaultInfo(
            executable = out,
            runfiles = info.default_runfiles,
            files = info.files,
        ),
    ]

opentitan_select_test = rule(
    implementation = _opentitan_select_test_impl,
    attrs = {
        "tests": attr.label_list(
            doc = "The list of test variants in the group.",
            providers = [OpenTitanTestInfo],
        ),
        "_preference": attr.label(
            default = "@lowrisc_opentitan//sw:exec_env",
            doc = "The preference list of execution environments.",
            providers = [BuildSettingInfo],
        ),
    },
    test = True,
)
