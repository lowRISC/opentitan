# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

def http_archive_or_local(local = None, **kwargs):
    if not local:
        http_archive(**kwargs)
    elif ("build_file" in kwargs or
          "build_file_content" in kwargs or
          "workspace_file" in kwargs or
          "workspace_file_content" in kwargs):
        native.new_local_repository(
            name = kwargs.get("name"),
            path = local,
            build_file = kwargs.get("build_file"),
            build_file_content = kwargs.get("build_file_content"),
            workspace_file = kwargs.get("workspace_file"),
            workspace_file_content = kwargs.get("workspace_file_content"),
        )
    else:
        native.local_repository(
            name = kwargs.get("name"),
            path = local,
        )
