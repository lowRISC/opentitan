# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_python//python:pip.bzl", "pip_install")
load("@python3//:defs.bzl", "interpreter")

_WHEEL_BUILD_FILE_CONTENTS = """\
package(default_visibility = ["//visibility:public"])

exports_files([
    "sanitized_requirements.txt",
])

filegroup(
    name = "all_wheels",
    srcs = glob(["**/*.whl"])
)
"""

def _pip_wheel_impl(rctx):
    # First, check if an existing pre-built Python wheels repo exists, and if
    # so, use it instead of building one.
    python_wheel_repo_path = rctx.os.environ.get(
        "BAZEL_PYTHON_WHEELS_REPO",
        None,
    )
    if python_wheel_repo_path:
        rctx.report_progress("Mounting existing Python wheels repo")
        rctx.symlink(python_wheel_repo_path, ".")
        return

    # If a pre-built Python wheels repo does not exist, we need to build it.
    rctx.report_progress("No Python wheels repo detected, building it instead")

    # First, we install the Python wheel package so we can build other wheels.
    args = [
        rctx.path(rctx.attr.python_interpreter),
        "-m",
        "pip",
        "install",
        "-U",
        "--ignore-installed",
        "wheel",
    ]
    rctx.report_progress("Installing the Python wheel package")
    result = rctx.execute(
        args,
        timeout = rctx.attr.timeout,
        quiet = rctx.attr.quiet,
    )
    if result.return_code:
        fail("pip_wheel failed: {} ({})".format(result.stdout, result.stderr))

    # Next, we download/build all the Python wheels for each requirement.
    args = [
        rctx.path(rctx.attr.python_interpreter),
        "-m",
        "pip",
        "wheel",
        "-r",
        rctx.path(rctx.attr.requirements),
        "-w",
        "./",
    ]
    rctx.report_progress("Pre-building Python wheels")
    result = rctx.execute(
        args,
        timeout = rctx.attr.timeout,
        quiet = rctx.attr.quiet,
    )
    if result.return_code:
        fail("pip_wheel failed: {} ({})".format(result.stdout, result.stderr))

    # Last, we generate a new Python requirements file that does not contain any
    # VCS links. We avoid just patching the existing python_requirements.txt
    # file, and instead generate a requirements file based on the wheels that
    # were built above. This enables us to make changes to the main
    # python_requirements.txt file without impacting this step.
    args = [rctx.path(rctx.attr._gen_requirements_script)]
    rctx.report_progress("Generating sanitzed requirements file")
    result = rctx.execute(
        args,
        timeout = rctx.attr.timeout,
        quiet = rctx.attr.quiet,
        working_directory = "./",
    )
    if result.return_code:
        fail("pip_wheel failed: {} ({})".format(result.stdout, result.stderr))

    # We need a BUILD file to load the downloaded Python packages.
    rctx.file(
        "BUILD.bazel",
        _WHEEL_BUILD_FILE_CONTENTS,
    )

pip_wheel = repository_rule(
    implementation = _pip_wheel_impl,
    attrs = {
        "python_interpreter": attr.label(
            default = interpreter,
            allow_single_file = True,
            doc = "Python interpreter to use.",
        ),
        "requirements": attr.label(
            default = "//:python-requirements.txt",
            allow_single_file = True,
            doc = "Python requirements file describing package dependencies.",
        ),
        "quiet": attr.bool(
            default = True,
            doc = "If True, suppress printing stdout/stderr to the terminal.",
        ),
        "timeout": attr.int(
            default = 300,
            doc = "Timeout (in seconds) on the rule's execution duration.",
        ),
        "_gen_requirements_script": attr.label(
            default = "//third_party/python:gen_requirements.sh",
            allow_single_file = True,
            doc = "Shell script that generates a requirements file without VCS links.",
            executable = True,
            cfg = "exec",
        ),
    },
    environ = ["BAZEL_PYTHON_WHEELS_REPO"],
)

def pip_deps():
    pip_wheel(
        name = "ot_python_wheels",
    )
    pip_install(
        name = "ot_python_deps",
        python_interpreter_target = interpreter,
        requirements = "@ot_python_wheels//:sanitized_requirements.txt",
        find_links = "@ot_python_wheels//:all_wheels",
        extra_pip_args = ["--no-index"],
    )
