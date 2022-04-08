# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

def riscv_compliance_repos():
    #new_git_repository(
    #    name = "riscv-compliance",
    #    build_file = Label("//third_party/riscv-compliance:BUILD.riscv-compliance.bazel"),
    #    remote = "https://github.com/riscv/riscv-compliance.git",
    #    commit = "5a978cfd444d5e640150d46703deda99057b2bbb",
    #    shallow_since = "1628817357 -0700",
    #    patches = [
    #        Label("//third_party/riscv-compliance:0001-Add-configurable-trap-alignment-and-entry-point-to-p.patch")
    #    ],
    #    patch_args = ["-p1"],
    #)

    # TODO(lowRISC/opentitan#11877)
    # For the time being, use a local repo, but it should really be replaced with
    # the an http_archive version of the git repo defined above. Note, we avoid using
    # git repos in order to support offline (airgapped) builds, which require building
    # the repository cache offline (which only works with http_archive). See
    # https://docs.bazel.build/versions/3.4.0/external.html#repository-rules
    #
    # Everything else in this directory is set up so that we can uncomment the above
    # without any other changes.
    native.new_local_repository(
        name = "riscv-compliance",
        path = "sw/vendor/riscv_compliance",
        build_file = "//third_party/riscv-compliance:BUILD.riscv-compliance.bazel",
    )
