# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# If you're planning to add to this file, please read
# //third_party/README.md first.

workspace(name = "lowrisc_opentitan")

# Bazel Embedded; Bazel platform configuration for embedded environments.
load("//third_party/bazel_embedded:repos.bzl", "bazel_embedded_repos")
bazel_embedded_repos()
load("//third_party/bazel_embedded:deps.bzl", "bazel_embedded_deps")
bazel_embedded_deps()

# The lowRISC LLVM Toolchain
load("//third_party/lowrisc_toolchain:repos.bzl", "lowrisc_toolchain_repos")
lowrisc_toolchain_repos()
load("//third_party/lowrisc_toolchain:deps.bzl", "lowrisc_toolchain_deps")
lowrisc_toolchain_deps()

# C/C++ Library Dependencies
load("//third_party/cc:repos.bzl", "cc_repos")
cc_repos()

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

# Rust Toolchain + crates.io Dependencies
load("//third_party/rust:repos.bzl", "rust_repos")
rust_repos()
load("//third_party/rust:deps.bzl", "rust_deps")
rust_deps()

# Protobuf Toolchain
load("//third_party/protobuf:repos.bzl", "protobuf_repos")
protobuf_repos()
load("//third_party/protobuf:deps.bzl", "protobuf_deps")
protobuf_deps()

# Various linters
load("//third_party/lint:repos.bzl", "lint_repos")
lint_repos()
load("//third_party/lint:deps.bzl", "lint_deps")
lint_deps()

# FreeRTOS; used by the OTTF
load("//third_party/freertos:repos.bzl", "freertos_repos")
freertos_repos()

# RISC-V Compliance Tests
load("//third_party/riscv-compliance:repos.bzl", "riscv_compliance_repos")
riscv_compliance_repos()
