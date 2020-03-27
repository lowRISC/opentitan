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

load("//devices:device_config.bzl", "device_config")

CORTEX_M0_DEVICE_CONFIG = device_config(
    cpu = "armv6-m",
    endian = "little",
    float_abi = "soft",
    fpu = "none",
)

# CORTEX_M1_DEVICE_CONFIG same as cortex m0

CORTEX_M3_DEVICE_CONFIG = device_config(
    cpu = "armv7-m",
    endian = "little",
    float_abi = "soft",
    fpu = "none",
)

# CORTEX_M4_DEVICE_CONFIG same as cortex m3

CORTEX_M4_FPU_DEVICE_CONFIG = device_config(
    cpu = "armv7-m",
    endian = "little",
    float_abi = "hard",
    fpu = "fpv4-sp-d16",
)

CORTEX_M7_DEVICE_CONFIG = device_config(
    cpu = "armv7e-m",
    endian = "little",
    float_abi = "soft",
    fpu = "none",
)

CORTEX_M7_FPU_DEVICE_CONFIG = device_config(
    cpu = "armv7e-m",
    endian = "little",
    float_abi = "hard",
    fpu = "fpv5-d16",
)

CORTEX_M_DEVICE_CONFIGS = [CORTEX_M0_DEVICE_CONFIG, CORTEX_M3_DEVICE_CONFIG, CORTEX_M4_FPU_DEVICE_CONFIG, CORTEX_M7_DEVICE_CONFIG, CORTEX_M7_FPU_DEVICE_CONFIG]
