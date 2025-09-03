# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

_ARCHIVE_MARKER_FILE = ".this.is.the.archive"

def _qemu_bazel_build_or_forward_impl(rctx):
    qemu_root = rctx.path(rctx.attr.qemu_src).dirname

    # Determine whether the source repo was overridden with a local source directory.
    if qemu_root.get_child(_ARCHIVE_MARKER_FILE).exists:
        # Symlink everything to the release directory. Also watch everything.
        for child in qemu_root.readdir():
            rctx.symlink(child, child.basename)
            if not child.is_dir:
                rctx.watch(child)
            elif child.is_dir:
                rctx.watch_tree(child)
    else:
        print(
            "QEMU source archive override detected:",
            "will be using {} as the source directory".format(qemu_root.realpath),
        )

        # Sanity checks.
        configure_script = qemu_root.get_child("configure")
        if not configure_script.exists:
            fail("There is no configure script in the source directory, did you override the QEMU source correctly?")

        # Run the build script which will produce a release archive
        release_archive = "build_archive.tar.gz"
        rctx.watch(rctx.attr._build_qemu)
        res = rctx.execute(
            [
                rctx.attr._build_qemu,
                qemu_root.realpath,
                release_archive,
            ],
            quiet = False,
        )
        if res.return_code != 0:
            fail("Failed to build QEMU")

        # Extract archive here.
        rctx.extract(rctx.path(release_archive))

        # Watch everything in the source directory.
        for child in qemu_root.readdir():
            # Skip the build directory because it can cause weird bazel behaviour:
            # this directory has symlinks and cycles.
            if not child.is_dir:
                rctx.watch(child)
            elif child.is_dir and child.basename != "build":
                rctx.watch_tree(child)

        # Create a single BUILD file that exports everything.
        rctx.file("BUILD", rctx.read(rctx.path(rctx.attr._build_file)))

qemu_bazel_build_or_forward = repository_rule(
    implementation = _qemu_bazel_build_or_forward_impl,
    attrs = {
        # This attribute is used to locate the source repository so that we don't have to guess
        # its name.
        "qemu_src": attr.label(doc = "This is a label to any file at the root of the QEMU source repository."),
        "_build_qemu": attr.label(
            default = ":build_qemu.sh",
            executable = True,
            cfg = "exec",
        ),
        "_build_file": attr.label(
            default = ":BUILD.qemu_opentitan.bazel",
        ),
    },
    # Allow the repository to be refetched by running
    # bazel configure fetch --force
    configure = True,
    # Make sure to refetch on restart.
    local = True,
)

def _qemu_opentitan_repos():
    QEMU_VERSION = "v9.2.0-2025-02-11"

    url = "/".join([
        "https://github.com/lowRISC/qemu/releases/download",
        QEMU_VERSION,
        "qemu-ot-earlgrey-{}-x86_64-unknown-linux-gnu.tar.gz".format(QEMU_VERSION),
    ])

    http_archive(
        name = "qemu_opentitan_src",
        url = url,
        build_file = Label(":BUILD.qemu_opentitan.bazel"),
        sha256 = "85091287ee67dee337968071b7d10d39d44bb582c90991eae3d61f11a13ccf29",
        patch_cmds = ["touch {}".format(_ARCHIVE_MARKER_FILE)],
    )

    qemu_bazel_build_or_forward(
        name = "qemu_opentitan",
        qemu_src = "@qemu_opentitan_src//:qemu_src",
    )

qemu = module_extension(
    implementation = lambda _: _qemu_opentitan_repos(),
)
