# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_python//python:defs.bzl", "py_binary")
load("@ot_python_deps//:requirements.bzl", "all_requirements", "requirement")

package(default_visibility = ["//visibility:public"])

exports_files(glob(["**"]))

py_binary(
    name = "otbn_build",
    srcs = ["otbn_build.py"],
    imports = [
        # //hw/ip/otbn/util:
        #   hw.ip.otbn.util.otbn_as
        #   hw.ip.otbn.util.otbn_ld
        "../hw/ip/otbn/util",
    ],
    deps = [
        "//hw/ip/otbn/util:otbn_as",
        "//hw/ip/otbn/util:otbn_ld",
        requirement("lz4"),
        requirement("pyelftools"),
    ],
)

py_binary(
    name = "build_info",
    srcs = ["build_info.py"],
    imports = [
        # //util:
        #   util.version_file
        ".",
    ],
    deps = [
        ":version_file",
    ],
)

py_test(
    name = "build_info_test",
    srcs = [
        "build_info.py",
        "build_info_test.py",
    ],
    imports = [
        # //util:
        #   util.build_info
        #   util.version_file
        ".",
    ],
    deps = [
        ":build_info",
        ":version_file",
    ],
)

py_binary(
    name = "cryptolib_build_info",
    srcs = ["cryptolib_build_info.py"],
    imports = [
        # //util:
        #   util.version_file
        ".",
    ],
    deps = [
        ":version_file",
    ],
)

py_library(
    name = "version_file",
    srcs = ["version_file.py"],
)

py_binary(
    name = "regtool",
    srcs = ["regtool.py"],
    imports = [
        # //util:
        #   util.reggen
        #   util.version_file
        ".",
    ],
    deps = [
        ":version_file",
        "//util/reggen:countermeasure",
        "//util/reggen:gen_cfg_md",
        "//util/reggen:gen_cheader",
        "//util/reggen:gen_dv",
        "//util/reggen:gen_fpv",
        "//util/reggen:gen_html",
        "//util/reggen:gen_json",
        "//util/reggen:gen_md",
        "//util/reggen:gen_rtl",
        "//util/reggen:gen_rust",
        "//util/reggen:gen_sec_cm_testplan",
        "//util/reggen:gen_selfdoc",
        "//util/reggen:gen_tock",
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
    imports = [
        # //util:
        #   util.generate_compilation_db
        ".",
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

cc_library(
    name = "bfv_decoder",
    srcs = ["bfv_decoder.c"],
    deps = [
        "//sw/device/silicon_creator/lib:error",
    ],
)

py_binary(
    name = "gen_stamped_tarball",
    srcs = ["gen_stamped_tarball.py"],
)
