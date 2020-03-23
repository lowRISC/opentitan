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

def remote_compiler(url, sha256, strip_prefix):
    return struct(url = url, sha256 = sha256, strip_prefix = strip_prefix)

def gcc_toolchain_info(full_version, linux_remote_compiler, windows_remote_compiler, mac_remote_compiler):
    return struct(full_version = full_version, linux_remote_compiler = linux_remote_compiler, windows_remote_compiler = windows_remote_compiler, mac_remote_compiler = mac_remote_compiler)

TOOLCHAIN_VERSIONS = {
    "9": gcc_toolchain_info(
        full_version = "9.2.1",
        linux_remote_compiler = remote_compiler(
            url = "https://developer.arm.com/-/media/Files/downloads/gnu-rm/9-2019q4/RC2.1/gcc-arm-none-eabi-9-2019-q4-major-x86_64-linux.tar.bz2?revision=6e63531f-8cb1-40b9-bbfc-8a57cdfc01b4&la=en&hash=F761343D43A0587E8AC0925B723C04DBFB848339",
            sha256 = "bcd840f839d5bf49279638e9f67890b2ef3a7c9c7a9b25271e83ec4ff41d177a",
            strip_prefix = "gcc-arm-none-eabi-9-2019-q4-major",
        ),
        windows_remote_compiler = remote_compiler(
            url = "https://developer.arm.com/-/media/Files/downloads/gnu-rm/9-2019q4/RC2.1/gcc-arm-none-eabi-9-2019-q4-major-win32.zip.bz2?revision=0dc1c4c9-8bba-4577-b57d-dc57d6f80c26&la=en&hash=F0B7C0475BA3213D5CC5DB576C75EC7D9BA3614A",
            sha256 = "e4c964add8d0fdcc6b14f323e277a0946456082a84a1cc560da265b357762b62",
            strip_prefix = "",
        ),
        mac_remote_compiler = remote_compiler(
            url = "https://developer.arm.com/-/media/Files/downloads/gnu-rm/9-2019q4/RC2.1/gcc-arm-none-eabi-9-2019-q4-major-mac.tar.bz2?revision=0108cc32-e125-409b-ae7b-b2d6d30bf69c&la=en&hash=8C90ACFF11212E0540D74DA6A4F6CEE7253CD13F",
            sha256 = "1249f860d4155d9c3ba8f30c19e7a88c5047923cea17e0d08e633f12408f01f0",
            strip_prefix = "gcc-arm-none-eabi-9-2019-q4-major",
        ),
    ),
}

def GetRemoteToolchainInfo(version, platform):
    return TOOLCHAIN_VERSIONS[version]
