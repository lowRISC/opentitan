# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

_RULES_PYTHON_VERSION = "0.39.0"

def python_repos():
    http_archive(
        name = "rules_python",
        sha256 = "62ddebb766b4d6ddf1712f753dac5740bea072646f630eb9982caa09ad8a7687",
        strip_prefix = "rules_python-{}".format(_RULES_PYTHON_VERSION),
        url = "https://github.com/bazelbuild/rules_python/releases/download/{}/rules_python-{}.tar.gz".format(
            _RULES_PYTHON_VERSION,
            _RULES_PYTHON_VERSION,
        ),
        patches = [Label("//third_party/python:airgapped-wheels-cache.patch")],
        patch_args = ["-p1"],
    )
