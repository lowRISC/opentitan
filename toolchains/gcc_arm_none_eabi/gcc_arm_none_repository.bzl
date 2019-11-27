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

load("//private:gcc_arm_none_versions.bzl", "GetRemoteToolchainInfo", "TOOLCHAIN_VERSIONS")

def _com_gcc_arm_none_repository_impl(repository_ctx):
    version = repository_ctx.attr.version
    remote_toolchain_info = GetRemoteToolchainInfo(version, "@bazel_tools//platforms:host_platform")
    repository_ctx.download_and_extract(
        url = remote_toolchain_info.linux_remote_compiler.url,
        sha256 = remote_toolchain_info.linux_remote_compiler.sha256,
        stripPrefix = remote_toolchain_info.linux_remote_compiler.strip_prefix,
    )
    repository_ctx.file(
        "BUILD",
        """
filegroup(
    name = "all",
    srcs = glob(["**/*"],exclude=["**/*.html","**/*.pdf"]),
    visibility = ['//visibility:public'],
)
exports_files(
    glob(["bin/**"])
)
""",
    )

gcc_arm_none_repository = repository_rule(
    _com_gcc_arm_none_repository_impl,
    attrs = {
        "version": attr.string(
            default = "9",
            doc = "GCC version, version 9 currently only version supported",
            values = TOOLCHAIN_VERSIONS.keys(),
        ),
    },
)

def gcc_arm_none_repository_preconfigured():
    gcc_arm_none_repository(
        name = "com_gcc_arm_none_eabi_compiler",
    )
