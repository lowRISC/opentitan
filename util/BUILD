# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_python//python:defs.bzl", "py_binary")
load("@ot_python_deps//:requirements.bzl", "all_requirements", "requirement")

package(default_visibility = ["//visibility:public"])

exports_files(glob(["**"]))

genrule(
    name = "ot_version_file",
    outs = ["ot_version.txt"],
    cmd = """awk '/BUILD_GIT_VERSION/ { print $$2 }' bazel-out/volatile-status.txt > $@""",
    stamp = 1,  # this provides volatile-status.txt
)

genrule(
    name = "full_version_file",
    outs = ["full_version.txt"],
    cmd = """cp -f bazel-out/volatile-status.txt $@""",
    stamp = 1,  # this provides volatile-status.txt
)

genrule(
    name = "scm_revision_file",
    outs = ["scm_revision.txt"],
    cmd = """awk '/BUILD_SCM_REVISION/ { print $$2 }' bazel-out/volatile-status.txt > $@""",
    stamp = 1,  # this provides volatile-status.txt
)

py_binary(
    name = "otbn_build",
    srcs = ["otbn_build.py"],
    imports = ["../hw/ip/otbn/util/"],
    deps = [
        requirement("pyelftools"),
        "//hw/ip/otbn/util:otbn_as",
        "//hw/ip/otbn/util:otbn_ld",
    ],
)

py_binary(
    name = "rom_chip_info",
    srcs = ["rom_chip_info.py"],
)

py_test(
    name = "rom_chip_info_test",
    srcs = [
        "rom_chip_info.py",
        "rom_chip_info_test.py",
    ],
)

py_binary(
    name = "regtool",
    srcs = ["regtool.py"],
    deps = [
        "//util/reggen:countermeasure",
        "//util/reggen:gen_cheader",
        "//util/reggen:gen_dv",
        "//util/reggen:gen_fpv",
        "//util/reggen:gen_html",
        "//util/reggen:gen_json",
        "//util/reggen:gen_rtl",
        "//util/reggen:gen_rust",
        "//util/reggen:gen_sec_cm_testplan",
        "//util/reggen:gen_selfdoc",
        "//util/reggen:ip_block",
        "//util/reggen:version",
        requirement("tabulate"),
    ],
)

py_test(
    name = "generate_compilation_db_test",
    srcs = [
        "generate_compilation_db.py",
        "generate_compilation_db_test.py",
    ],
)

py_binary(
    name = "run_manual_tests",
    srcs = [
        "run_manual_tests.py",
    ],
    deps = [
        requirement("typer"),
        requirement("hjson"),
        requirement("rich"),
        requirement("pluralizer"),
    ],
)

py_binary(
    name = "fusesoc_build",
    srcs = ["fusesoc_build.py"],
    deps = all_requirements,
)
