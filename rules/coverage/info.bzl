# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

def create_cc_instrumented_files_info(ctx, metadata_files):
    """Creates an InstrumentedFilesInfo provider to be added to the target.

    This is a simplified version of the same function in bazel's `cc_helper.bzl`.

    Args:
      ctx: The rule context.
      metadata_files: A list of metadata files to be added to the provider.

    Returns:
      An InstrumentedFilesInfo provider.
    """
    cc_config = ctx.fragments.cpp
    info = coverage_common.instrumented_files_info(
        ctx = ctx,
        source_attributes = ["srcs", "hdrs"],
        dependency_attributes = ["implementation_deps", "deps", "data"],
        extensions = [".c", ".h", ".inc", ".s", ".S"],
        metadata_files = metadata_files,
    )
    return info
