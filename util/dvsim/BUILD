# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_python//python:defs.bzl", "py_binary")
load("@ot_python_deps//:requirements.bzl", "requirement")

package(default_visibility = ["//visibility:public"])

py_library(
    name = "utils",
    srcs = ["utils.py"],
    deps = [
        requirement("hjson"),
        requirement("mistletoe"),
        requirement("premailer"),
    ],
)

py_library(
    name = "sim_utils",
    srcs = ["sim_utils.py"],
)

py_library(
    name = "msg_buckets",
    srcs = [
        "MsgBucket.py",
        "MsgBuckets.py",
    ],
    deps = [
        ":utils",
    ],
)

py_library(
    name = "modes",
    srcs = ["Modes.py"],
    deps = [
        ":utils",
    ],
)

py_library(
    name = "timer",
    srcs = ["Timer.py"],
)

py_library(
    name = "status_printer",
    srcs = ["StatusPrinter.py"],
    deps = [
        requirement("enlighten"),
    ],
)

py_library(
    name = "launcher",
    srcs = [
        "Launcher.py",
        "LauncherFactory.py",
        "LocalLauncher.py",
        "LsfLauncher.py",
    ],
    deps = [
        ":utils",
    ],
)

py_library(
    name = "deploy",
    srcs = ["Deploy.py"],
    deps = [
        ":launcher",
        ":sim_utils",
        ":utils",
        requirement("tabulate"),
    ],
)

py_library(
    name = "scheduler",
    srcs = ["Scheduler.py"],
    deps = [
        ":launcher",
        ":status_printer",
        ":timer",
        ":utils",
    ],
)

py_library(
    name = "cfg_json",
    srcs = ["CfgJson.py"],
    deps = [
        ":utils",
    ],
)

py_library(
    name = "flow_cfg",
    srcs = ["FlowCfg.py"],
    deps = [
        ":cfg_json",
        ":launcher",
        ":scheduler",
        ":utils",
        requirement("hjson"),
    ],
)

py_library(
    name = "oneshot_cfg",
    srcs = ["OneShotCfg.py"],
    deps = [
        ":deploy",
        ":flow_cfg",
        ":modes",
        ":utils",
    ],
)

py_library(
    name = "lint_cfg",
    srcs = ["LintCfg.py"],
    deps = [
        ":msg_buckets",
        ":oneshot_cfg",
        ":utils",
        requirement("tabulate"),
    ],
)

py_library(
    name = "formal_cfg",
    srcs = ["FormalCfg.py"],
    deps = [
        ":oneshot_cfg",
        ":utils",
        requirement("hjson"),
        requirement("tabulate"),
    ],
)

py_library(
    name = "cdc_cfg",
    srcs = ["CdcCfg.py"],
    deps = [
        ":lint_cfg",
        ":msg_buckets",
        ":utils",
        requirement("tabulate"),
    ],
)

py_library(
    name = "rdc_cfg",
    srcs = ["RdcCfg.py"],
    deps = [
        ":cdc_cfg",
    ],
)

py_library(
    name = "testplan",
    srcs = ["Testplan.py"],
    deps = [
        requirement("hjson"),
        requirement("mistletoe"),
        requirement("tabulate"),
    ],
)

py_library(
    name = "sim_results",
    srcs = ["SimResults.py"],
    deps = [
        ":testplan",
    ],
)

py_library(
    name = "sim_cfg",
    srcs = ["SimCfg.py"],
    deps = [
        ":deploy",
        ":flow_cfg",
        ":modes",
        ":sim_results",
        ":testplan",
        ":utils",
        requirement("tabulate"),
    ],
)

py_library(
    name = "syn_cfg",
    srcs = ["SynCfg.py"],
    deps = [
        ":oneshot_cfg",
        ":utils",
        requirement("hjson"),
        requirement("tabulate"),
    ],
)

py_library(
    name = "cfg_factory",
    srcs = ["CfgFactory.py"],
    deps = [
        ":cdc_cfg",
        ":cfg_json",
        ":formal_cfg",
        ":lint_cfg",
        ":sim_cfg",
        ":syn_cfg",
    ],
)

py_binary(
    name = "dvsim",
    srcs = ["dvsim.py"],
    deps = [
        ":cfg_factory",
        ":deploy",
        ":launcher",
        ":timer",
        ":utils",
    ],
)
