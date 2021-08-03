# MIT License
#
# Copyright (c) 2019 Nathaniel Brough
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in all
# copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
# SOFTWARE.

load("//devices/riscv32:riscv32.bzl", "RISCV32_DEVICE_CONFIGS")
load(
    ":lowrisc_toolchain_rv32imc.bzl",
    "compiler_components",
    "lowrisc_toolchain_rv32imc_toolchain",
)

package(default_visibility = ["//visibility:public"])

_DEVICE_CONFIGS = RISCV32_DEVICE_CONFIGS

compiler_components(
    injected_hdr_deps = "@bazel_embedded_upstream_toolchain//:injected_headers",
    system_hdr_deps = "@bazel_embedded_upstream_toolchain//:polyfill",
)

[lowrisc_toolchain_rv32imc_toolchain(
    name = "riscv32_unknown_elf_" + cfg.cpu + "_" + cfg.fpu,
    architecture = cfg.cpu,
    compiler_components = ":compiler_components",
    endian = cfg.endian,
    float_abi = cfg.float_abi,
    fpu = cfg.fpu,
) for cfg in _DEVICE_CONFIGS]
