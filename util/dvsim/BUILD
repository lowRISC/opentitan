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
    imports = [
        # //util/dvsim:
        #   util.dvsim.MsgBucket
        #   util.dvsim.utils
        ".",
    ],
    deps = [
        ":utils",
        requirement("hjson"),
    ],
)

py_library(
    name = "modes",
    srcs = [
        "Regression.py",
        "Test.py",
        "modes.py",
    ],
    imports = [
        # //util/dvsim:
        #   util.dvsim.Test
        #   util.dvsim.modes
        #   util.dvsim.utils
        ".",
    ],
    deps = [
        ":utils",
    ],
)

py_library(
    name = "job_time",
    srcs = ["JobTime.py"],
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
        "SGE.py",
        "SgeLauncher.py",
        "qsubopts.py",
    ],
    imports = [
        # //util/dvsim:
        #   util.dvsim.Launcher
        #   util.dvsim.LocalLauncher
        #   util.dvsim.LsfLauncher
        #   util.dvsim.SGE
        #   util.dvsim.SgeLauncher
        #   util.dvsim.qsubopts
        #   util.dvsim.utils
        ".",
    ],
    deps = [
        ":job_time",
        ":utils",
    ],
)

py_library(
    name = "deploy",
    srcs = ["Deploy.py"],
    imports = [
        # //util/dvsim:
        #   util.dvsim.JobTime
        #   util.dvsim.LauncherFactory
        #   util.dvsim.sim_utils
        #   util.dvsim.utils
        ".",
    ],
    deps = [
        ":job_time",
        ":launcher",
        ":sim_utils",
        ":utils",
        requirement("tabulate"),
    ],
)

py_library(
    name = "scheduler",
    srcs = ["Scheduler.py"],
    imports = [
        # //util/dvsim:
        #   util.dvsim.Launcher
        #   util.dvsim.StatusPrinter
        #   util.dvsim.Timer
        #   util.dvsim.utils
        ".",
    ],
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
    imports = [
        # //util/dvsim:
        #   util.dvsim.utils
        ".",
    ],
    deps = [
        ":utils",
    ],
)

py_library(
    name = "flow_cfg",
    srcs = ["FlowCfg.py"],
    imports = [
        # //util/dvsim:
        #   util.dvsim.CfgJson
        #   util.dvsim.LauncherFactory
        #   util.dvsim.Scheduler
        #   util.dvsim.utils
        ".",
    ],
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
    imports = [
        # //util/dvsim:
        #   util.dvsim.Deploy
        #   util.dvsim.FlowCfg
        #   util.dvsim.modes
        #   util.dvsim.utils
        ".",
    ],
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
    imports = [
        # //util/dvsim:
        #   util.dvsim.MsgBuckets
        #   util.dvsim.OneShotCfg
        #   util.dvsim.utils
        ".",
    ],
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
    imports = [
        # //util/dvsim:
        #   util.dvsim.OneShotCfg
        #   util.dvsim.utils
        ".",
    ],
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
    imports = [
        # //util/dvsim:
        #   util.dvsim.LintCfg
        ".",
    ],
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
    imports = [
        # //util/dvsim:
        #   util.dvsim.LintCfg
        ".",
    ],
    deps = [
        ":cdc_cfg",
        ":lint_cfg",
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
    imports = [
        # //util/dvsim:
        #   util.dvsim.Testplan
        ".",
    ],
    deps = [
        ":testplan",
    ],
)

py_library(
    name = "sim_cfg",
    srcs = ["SimCfg.py"],
    imports = [
        # //util/dvsim:
        #   util.dvsim.Deploy
        #   util.dvsim.FlowCfg
        #   util.dvsim.Regression
        #   util.dvsim.SimResults
        #   util.dvsim.Test
        #   util.dvsim.Testplan
        #   util.dvsim.modes
        #   util.dvsim.utils
        ".",
    ],
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
    imports = [
        # //util/dvsim:
        #   util.dvsim.OneShotCfg
        #   util.dvsim.utils
        ".",
    ],
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
    imports = [
        # //util/dvsim:
        #   util.dvsim.CdcCfg
        #   util.dvsim.CfgJson
        #   util.dvsim.FormalCfg
        #   util.dvsim.LintCfg
        #   util.dvsim.RdcCfg
        #   util.dvsim.SimCfg
        #   util.dvsim.SynCfg
        ".",
    ],
    deps = [
        ":cdc_cfg",
        ":cfg_json",
        ":formal_cfg",
        ":lint_cfg",
        ":rdc_cfg",
        ":sim_cfg",
        ":syn_cfg",
    ],
)

py_binary(
    name = "dvsim",
    srcs = ["dvsim.py"],
    imports = [
        # //util/dvsim:
        #   util.dvsim.CfgFactory
        #   util.dvsim.Deploy
        #   util.dvsim.Launcher
        #   util.dvsim.LauncherFactory
        #   util.dvsim.LocalLauncher
        #   util.dvsim.SgeLauncher
        #   util.dvsim.Timer
        #   util.dvsim.utils
        ".",
    ],
    deps = [
        ":cfg_factory",
        ":deploy",
        ":launcher",
        ":timer",
        ":utils",
    ],
)
