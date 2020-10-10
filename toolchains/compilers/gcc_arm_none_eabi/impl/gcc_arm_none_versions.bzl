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
    "full_version": "9.2.1",
    "remote_compiler": {
        "url": "https://developer.arm.com/-/media/Files/downloads/gnu-rm/9-2020q2/gcc-arm-none-eabi-9-2020-q2-update-win32.zip?revision=95631fd0-0c29-41f4-8d0c-3702650bdd74&la=en&hash=D2C7F7C52183A8818AE6179AB87AA7CF6B1AE275",
        "sha256": "49d6029ecd176deaa437a15b3404f54792079a39f3b23cb46381b0e6fbbe9070",
        "strip_prefix": "",
    },
}

_PLATFORM_SPECIFIC_CONFIGS_9 = {
    "linux": {
        "full_version": "9.2.1",
        "remote_compiler": {
            "url": "https://developer.arm.com/-/media/Files/downloads/gnu-rm/9-2019q4/RC2.1/gcc-arm-none-eabi-9-2019-q4-major-x86_64-linux.tar.bz2?revision=6e63531f-8cb1-40b9-bbfc-8a57cdfc01b4&la=en&hash=F761343D43A0587E8AC0925B723C04DBFB848339",
            "sha256": "bcd840f839d5bf49279638e9f67890b2ef3a7c9c7a9b25271e83ec4ff41d177a",
            "strip_prefix": "gcc-arm-none-eabi-9-2019-q4-major",
        },
    },
    "windows": _WINDOWS,
    "windows server 2019": _WINDOWS,
    "windows 10": _WINDOWS,
    "mac os x": {
        "full_version": "9.2.1",
        "remote_compiler": {
            "url": "https://developer.arm.com/-/media/Files/downloads/gnu-rm/9-2019q4/RC2.1/gcc-arm-none-eabi-9-2019-q4-major-mac.tar.bz2?revision=0108cc32-e125-409b-ae7b-b2d6d30bf69c&la=en&hash=8C90ACFF11212E0540D74DA6A4F6CEE7253CD13F",
            "sha256": "1249f860d4155d9c3ba8f30c19e7a88c5047923cea17e0d08e633f12408f01f0",
            "strip_prefix": "gcc-arm-none-eabi-9-2019-q4-major",
        },
    },
}

TOOLCHAIN_VERSIONS = {
    "9": _PLATFORM_SPECIFIC_CONFIGS_9,
}

def get_platform_specific_config(version, os_name):
    if version not in TOOLCHAIN_VERSIONS:
        fail("Toolchain configuration not available for version: ", version)
    if os_name not in TOOLCHAIN_VERSIONS[version].keys():
        fail("OS configuration not available for: {}".format(os_name))
    return TOOLCHAIN_VERSIONS[version][os_name]
