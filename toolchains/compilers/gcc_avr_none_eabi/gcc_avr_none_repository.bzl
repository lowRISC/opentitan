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

load("//toolchains/tools/include_tools:include_tools.bzl", "include_tools")

def _com_gcc_avr_none_repository_impl(repository_ctx):
    repository_ctx.download_and_extract(
        url = "https://www.microchip.com/wwwregister/default.aspx?ReturnURL=http://ww1.microchip.com/downloads/Secure/en/DeviceDoc/avr8-gnu-toolchain-3.6.2.1759-linux.any.x86_64.tar.gz",
        sha256 = "f2acca334fd22228892e60e1df12de9551e72d128b7fb3c4ebc4fc2de5c76655",
        stripPrefix = "avr8-gnu-toolchain-linux_x86_64",
        type = "tar.gz",
    )
    response = repository_ctx.execute(include_tools.ShellCommand("bin/avr-cpp"))
    include_flags = include_tools.ProccessResponse(response.stderr)
    include_bazel_template_input = include_tools.CommandLineToTemplateString(include_flags)
    repository_ctx.file(
        "defs.bzl",
        "SYSTEM_INCLUDE_COMMAND_LINE = " + include_bazel_template_input,
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

gcc_avr_none_repository = repository_rule(
    _com_gcc_avr_none_repository_impl,
    attrs = {
        "version": attr.string(
            default = "5.4.0",
            doc = "GCC version, version 5.4.0 currently only version supported",
            values = ["5.4.0"],
        ),
    },
)

def gcc_avr_none_compiler():
    gcc_avr_none_repository(
        name = "com_gcc_avr_none_eabi_compiler",
    )
