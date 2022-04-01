# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Dependencies that linter rules depend on."""

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

def lowrisc_misc_linters_dependencies():
  """Declares workspaces linting rules depend on.
  Make sure to call this in your WORKSPACE file."""
  http_archive(
      name = "rules_python",
      url = "https://github.com/bazelbuild/rules_python/releases/download/0.5.0/rules_python-0.5.0.tar.gz",
      sha256 = "cd6730ed53a002c56ce4e2f396ba3b3be262fd7cb68339f0377a45e8227fe332",
  )
