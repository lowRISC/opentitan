# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

_ARCHIVE_MARKER_FILE = ".this.is.the.archive"

def _qemu_bazel_build_or_forward_impl(rctx):
    qemu_root = rctx.path(rctx.attr.qemu_src).dirname

    # Symlink everything to the source directory, except the BUILD file.
    for child in qemu_root.readdir():
        if child.basename not in ["BUILD", "BUILD.bazel"]:
            rctx.symlink(child, child.basename)

            # We also want to watch any directory, except the build/ directory (since we
            # are going to change it).
            if child.basename != "build" and child.is_dir:
                rctx.watch_tree(child)

    # Determine whether the source repo was overridden with a local source directory.
    if not qemu_root.get_child(_ARCHIVE_MARKER_FILE).exists:
        print(
            "QEMU source archive override detected:",
            "will be using {} as the source directory".format(qemu_root.realpath),
        )

        # Sanity checks.
        configure_script = rctx.path("configure")
        if not configure_script.exists:
            fail("There is no configure script in the source directory, did you override the QEMU source correctly?")

        build_dir = rctx.path("build")
        if not build_dir.exists:
            fail("There is no build/ directory in the source directory, you must create one manually")

        # Only re-run the configure script if needed.
        config_host_mak = build_dir.get_child("config-host.mak")
        if not config_host_mak.exists:
            print("Configuring QEMU...")
            res = rctx.execute(
                [
                    # We use the real path of the configure script because it records the $PWD when running.
                    # If we used the repo path, it would lead to a unable path outside of Bazel and therefore
                    # the build directory would be broken outside of Bazel.
                    configure_script.realpath,
                    "--target-list=riscv32-softmmu",
                    "--without-default-features",
                    "--enable-tcg",
                    "--enable-tools",
                    "--enable-trace-backends=log",
                ],
                working_directory = "build",
            )

            # Write the configure output and fail in case of error.
            rctx.file("build/configure.stdout.log", res.stdout)
            rctx.file("build/configure.stderr.log", res.stderr)
            if res.return_code != 0:
                fail("QEMU configure script failed, see {}/configure.{{stdout,stderr}}.log for the log".format(build_dir.realpath))
        else:
            print("Skipping configure, if you want to re-run, delete {}".format(config_host_mak.realpath))

        print("Building QEMU...")
        for target in ["qemu-system-riscv32", "qemu-img"]:
            res = rctx.execute(
                [
                    "ninja",
                    target,
                ],
                working_directory = "build",
            )

            # Write the configure output and fail in case of error.
            rctx.file("build/build.{}.stdout.log".format(target), res.stdout)
            rctx.file("build/build.{}.stderr.log".format(target), res.stderr)
            if res.return_code != 0:
                fail("QEMU build failed, see {}/build.{}.{{stdout,stderr}}.log for the log".format(build_dir.realpath, target))

    # Create a single BUILD file that exports everything.
    rctx.file("BUILD", rctx.read(rctx.path(Label(":BUILD.qemu_opentitan.bazel"))))

qemu_bazel_build_or_forward = repository_rule(
    implementation = _qemu_bazel_build_or_forward_impl,
    attrs = {
        # This attribute is used to locate the source repository so that we don't have to guess
        # its name.
        "qemu_src": attr.label(doc = "This is a label to any file at the root of the QEMU source repository."),
    },
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
        qemu_src = "@qemu_opentitan_src//:BUILD",
    )

qemu = module_extension(
    implementation = lambda _: _qemu_opentitan_repos(),
)
