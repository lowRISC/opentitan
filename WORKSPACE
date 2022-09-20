# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# If you're planning to add to this file, please read
# //third_party/README.md first.

workspace(name = "lowrisc_opentitan")

# CRT is the Compiler Repository Toolkit.  It contains the configuration for
# the windows compiler.
load("//third_party/crt:repos.bzl", "crt_repos")
crt_repos()
load("@crt//:repos.bzl", "crt_repos")
crt_repos()
load("@crt//:deps.bzl", "crt_deps")
crt_deps()
load("@crt//config:registration.bzl", "crt_register_toolchains")
crt_register_toolchains(riscv32 = True)

# Tools for release automation
load("//third_party/github:repos.bzl", "github_tools_repos")
github_tools_repos()

# Various linters
# Note: load this early so the preferred version of
# com_github_bazel_builtools wins.
load("//third_party/lint:repos.bzl", "lint_repos")
lint_repos()
load("//third_party/lint:deps.bzl", "lint_deps")
lint_deps()

# Go Toolchain
load("//third_party/go:repos.bzl", "go_repos")
go_repos()
load("//third_party/go:deps.bzl", "go_deps")
go_deps()

# Python Toolchain + PIP Dependencies
load("//third_party/python:repos.bzl", "python_repos")
python_repos()
load("//third_party/python:deps.bzl", "python_deps")
python_deps()
load("//third_party/python:pip.bzl", "pip_deps")
pip_deps()

# Google/Bazel dependencies.  This needs to be after Python initialization
# so that our preferred python configuration takes precedence.
load("//third_party/google:repos.bzl", "google_repos")
google_repos()
load("//third_party/google:deps.bzl", "google_deps")
google_deps()

# Rust Toolchain + crates.io Dependencies
load("//third_party/rust:repos.bzl", "rust_repos")
rust_repos()
load("//third_party/rust:deps.bzl", "rust_deps")
rust_deps()

# Cargo Raze dependencies
load("//third_party/cargo_raze:repos.bzl", "raze_repos")
raze_repos()
load("//third_party/cargo_raze:deps.bzl", "raze_deps")
raze_deps()
# The raze instructions would have us call `cargo_raze_transitive_deps`, but that
# wants to re-instantiate rules_rust and mess up our rust configuration.
# Instead, we perform the single other action that transitive_deps would perform:
# load and instantiate `rules_foreign_cc_dependencies`.
#load("@cargo_raze//:transitive_deps.bzl", "cargo_raze_transitive_deps")
#cargo_raze_transitive_deps()
load("@rules_foreign_cc//foreign_cc:repositories.bzl", "rules_foreign_cc_dependencies")
rules_foreign_cc_dependencies()

# Protobuf Toolchain
load("//third_party/protobuf:repos.bzl", "protobuf_repos")
protobuf_repos()
load("//third_party/protobuf:deps.bzl", "protobuf_deps")
protobuf_deps()

# FreeRTOS; used by the OTTF
load("//third_party/freertos:repos.bzl", "freertos_repos")
freertos_repos()

# RISC-V Compliance Tests
load("//third_party/riscv-compliance:repos.bzl", "riscv_compliance_repos")
riscv_compliance_repos()

# Bitstreams from https://storage.googleapis.com/opentitan-bitstreams/
load("//rules:bitstreams.bzl", "bitstreams_repo")
bitstreams_repo(name = "bitstreams")

# Setup for linking in external test hooks.
load("//rules:hooks_setup.bzl", "hooks_setup")
hooks_setup(
    name = "hooks_setup",
    dummy = "sw/device/tests/closed_source",
)

# Declare the external test_hooks repository.
load("@hooks_setup//:repos.bzl", "hooks_repo")
hooks_repo(name = "manufacturer_test_hooks")

# The nonhermetic_repo imports environment variables needed to run vivado.
load("//rules:nonhermetic.bzl", "nonhermetic_repo")
nonhermetic_repo(name = "nonhermetic")
