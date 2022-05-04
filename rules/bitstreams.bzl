# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load("@python3//:defs.bzl", "interpreter")

def _bitstreams_repo_impl(rctx):
    result = rctx.execute(
        [
            rctx.path(rctx.attr.python_interpreter),
            rctx.attr._cache_manager,
            "--build-file=BUILD.bazel",
            "--bucket-url={}".format(rctx.attr.bucket_url),
            "--cache={}".format(rctx.attr.cache),
            "--refresh-time={}".format(rctx.attr.refresh_time),
        ],
        quiet = False,
    )
    if result.return_code != 0:
        fail("Bitstream cache not initialized properly.")

# The bitstream repo is evaluated on every invocation of bazel.
# Once the cache is initialized, a typical invocation will find the latest
# cached bitstream and configure it for use as a test artifact.
#
# The `refresh_time` sets the interval at which the cache manager will
# check for new bitstreams.
#
# By default, the cache manager will configure the latest available bitstream
# as the default bitstream.  It will refresh every 18 hours.
#
# The behavior of the cache manager can be constrolled via the BITSTREAM
# environment variable.  The environment variable can be any command line
# arguments accepted by the cache manager script.
#
# For example, to force a refresh of the cache:
# BITSTREAM=--refresh bazel build @bitstreams//...
#
# To use an exact bitstream in a test:
# BITSTREAM=3732655dbd225b5c1ae94a79b54cc9dc8cd8e391 bazel test <label>
#
# You can use any valid git commit identifier to select a bitstream:
# BITSTREAM=HEAD~1 bazel test <label>
#
# If you ask for a bitstream that does not exist in the GCP bucket, the
# next oldest bitstream will be chosen.
bitstreams_repo = repository_rule(
    implementation = _bitstreams_repo_impl,
    attrs = {
        "bucket_url": attr.string(
            doc = "Location of the GCP bitstream bucket.",
            default = "https://storage.googleapis.com/opentitan-bitstreams/",
        ),
        "cache": attr.string(
            doc = "Location of bitstreams cache.",
            default = "~/.cache/opentitan-bitstreams",
        ),
        "refresh_time": attr.int(
            doc = "How often to check for new bitstreams (seconds).",
            default = 18 * 3600,  # Refresh every 18h
        ),
        "python_interpreter": attr.label(
            default = interpreter,
            allow_single_file = True,
            doc = "Python interpreter to use.",
        ),
        "_cache_manager": attr.label(
            default = Label("//rules/scripts:bitstreams_workspace.py"),
            allow_files = True,
        ),
    },
    environ = ["BITSTREAM"],
    local = True,
)
