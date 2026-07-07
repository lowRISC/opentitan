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

def _coverage_sources_aspect_impl(target, ctx):
    """Collects source files for coverage analysis.

    This aspect traverses the dependency graph to gather all files necessary for
    coverage reporting. This specific output group can be explicitly requested
    to ensure that the generated source files are available for analysis.

    ```
    bazel build \
      --output_groups=coverage_sources \
      --aspects=rules/coverage/info.bzl%coverage_sources_aspect \
      <targets...>
    ```

    Returns:
        An OutputGroupInfo provider containing the `coverage_sources` group.
    """

    sources = []

    if InstrumentedFilesInfo in target:
        info = target[InstrumentedFilesInfo]
        sources.append(info.metadata_files)
        sources.append(info.instrumented_files)

    if OutputGroupInfo in target:
        info = target[OutputGroupInfo]
        if "coverage_sources" in info:
            sources.append(info.coverage_sources)

    return [
        OutputGroupInfo(
            coverage_sources = depset(transitive = sources),
        ),
    ]

coverage_sources_aspect = aspect(
    implementation = _coverage_sources_aspect_impl,
)
