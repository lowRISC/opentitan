# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_python//python:defs.bzl", "py_binary")
load("@ot_python_deps//:requirements.bzl", "all_requirements", "requirement")

package(default_visibility = ["//visibility:public"])

exports_files(glob(["**"]))

filegroup(
    name = "doc_files",
    srcs = glob(["**/*.md"]) + [
        "//util/design:doc_files",
        "//util/dtgen:doc_files",
        "//util/dvsim:doc_files",
        "//util/fpvgen:doc_files",
        "//util/i2csvg:doc_files",
        "//util/ipgen:doc_files",
        "//util/reggen:doc_files",
        "//util/tlgen:doc_files",
        "//util/topgen:doc_files",
        "//util/uvmdvgen:doc_files",
    ],
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
        "//util/reggen:gen_tock",
        "//util/reggen:ip_block",
        "//util/reggen:systemrdl_exporter",
        "//util/reggen:version",
        requirement("tabulate"),
    ],
)

py_binary(
    name = "autogen_dif",
    srcs = ["autogen_dif.py"],
    data = [
        "//util/make_new_dif:tpl_files",
    ],
    deps = [
        ":repo_top",
        "//util/make_new_dif:ip",
        requirement("hjson"),
        requirement("mako"),
    ],
)

py_binary(
    name = "dttool",
    srcs = ["dttool.py"],
    data = [
        "//util/dtgen:tpl_files",
    ],
    deps = [
        "//util/dtgen:helper",
        "//util/dtgen:ipgen_ext",
        "//util/ipgen",
        "//util/reggen:ip_block",
        "//util/reggen:version",
        "//util/topgen",
        requirement("mako"),
    ],
)

py_binary(
    name = "gen_testutils",
    srcs = ["gen_testutils.py"],
    deps = [
        "//util/autogen_testutils",
        "//util/topgen",
        requirement("mako"),
        requirement("hjson"),
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

py_library(
    name = "version_file",
    srcs = ["version_file.py"],
)

py_library(
    name = "repo_top",
    srcs = ["repo_top.py"],
)

cc_library(
    name = "bfv_decoder",
    srcs = ["bfv_decoder.c"],
    deps = [
        "//sw/device/silicon_creator/lib:error",
    ],
)

[
    py_binary(
        name = "mdbook_{}".format(preprocessor),
        srcs = ["mdbook_{}.py".format(preprocessor)],
    )
    for preprocessor in [
        "code_snippet",
        "dashboard",
        "doxygen",
        "otbn",
        "readme2index",
        "reggen",
        "testplan",
    ]
]

py_binary(
    name = "mdbook_toolversion",
    srcs = ["mdbook_toolversion.py"],
    deps = ["//hw:check_tool_requirements"],
)

py_binary(
    name = "gen_stamped_tarball",
    srcs = ["gen_stamped_tarball.py"],
)
