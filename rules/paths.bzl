# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Path manipulation utilities."""

def to_rlocation_path(ctx, file):
    """Computes the canonical rlocation path for a `File`.

    This produces the same value as the `$(rlocationpath)` variable expansion.
    Based on the canonical implementation in bazel-contrib/bazel-lib:
    https://github.com/bazel-contrib/bazel-lib/blob/c439ca6e64c9756ba976d6708bf573b396c61b84/lib/private/paths.bzl#L79

    Args:
        ctx: Starlark rule execution context.
        file: A `File` object.

    Returns:
        The rlocation path string to pass to runfiles `rlocation`.
    """
    if file.short_path.startswith("../"):
        return file.short_path[3:]
    return ctx.workspace_name + "/" + file.short_path
