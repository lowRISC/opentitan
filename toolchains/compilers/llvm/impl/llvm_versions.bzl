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

_WINDOWS = {
    "full_version": "11.0",
    "remote_compiler": {
        "url": "",
        "sha256": "",
        "strip_prefix": "",
    },
}

_PLATFORM_SPECIFIC_CONFIGS_11 = {
    "linux": {
        "full_version": "11.0",
        "remote_compiler": {
            "url": "https://github.com/llvm/llvm-project/releases/download/llvmorg-11.0.1/clang+llvm-11.0.1-x86_64-linux-gnu-ubuntu-16.04.tar.xz",
            "sha256": "67f18660231d7dd09dc93502f712613247b7b4395e6f48c11226629b250b53c5",
            "strip_prefix": "clang+llvm-11.0.1-x86_64-linux-gnu-ubuntu-16.04",
        },
    },
    "windows": _WINDOWS,
    "windows server 2019": _WINDOWS,
    "windows 10": _WINDOWS,
    "mac os x": {
        "full_version": "11.0",
        "remote_compiler": {
            "url": "https://github.com/llvm/llvm-project/releases/download/llvmorg-10.0.0/clang+llvm-10.0.0-x86_64-apple-darwin.tar.xz",
            "sha256": "",
            "strip_prefix": "clang+llvm-10.0.0-x86_64-apple-darwin",
        },
    },
}

TOOLCHAIN_VERSIONS = {
    "11": _PLATFORM_SPECIFIC_CONFIGS_11,
}

def get_platform_specific_config(version, os_name):
    if version not in TOOLCHAIN_VERSIONS:
        fail("Toolchain configuration not available for version: ", version)
    if os_name not in TOOLCHAIN_VERSIONS[version].keys():
        fail("OS configuration not available for: {}".format(os_name))
    return TOOLCHAIN_VERSIONS[version][os_name]
