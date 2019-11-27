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

package(default_visibility = ["//visibility:public"])

cc_toolchain_suite(
    name = "gcc_multi_platform",
    toolchains = {
        "armv7e-m": ":arm_none_eabi_toolchain",
    },
)

load(
    "@com_gcc_arm_none_eabi//:gcc_arm_none_toolchain_config.bzl",
    "gcc_arm_none_toolchain",
    "gcc_arm_none_toolchain_config",
)

gcc_arm_none_toolchain(
    name = "arm_none_eabi_toolchain",
    toolchain_config = ":arm_none_eabi_stm32h7_config",
    toolchain_identifier = "arm-none-eabi-toolchian",
)

gcc_arm_none_toolchain_config(
    name = "arm_none_eabi_stm32h7_config",
    arch = "armv7e-m",
    dynamic_memory = False,
    exceptions = False,
    float_abi = "hard",
    fpu = "fpv5-d16",
    rtti = False,
    toolchain_identifier = "arm-none-eabi-toolchain",
)
