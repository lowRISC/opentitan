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

workspace(name = "bazel_embedded")

load("//:bazel_embedded_deps.bzl", "bazel_embedded_deps")

bazel_embedded_deps()

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")
load("@bazel_tools//tools/build_defs/repo:git.bzl", "git_repository")

git_repository(
    name = "rules_cc",
    commit = "a636005ba28c0344da5110bd8532184c74b6ffdf",
    remote = "https://github.com/bazelbuild/rules_cc.git",
    shallow_since = "1583316607 -0800",
)

http_archive(
    name = "bazel_skylib",
    urls = [
        "https://github.com/bazelbuild/bazel-skylib/releases/download/1.0.3/bazel-skylib-1.0.3.tar.gz",
        "https://mirror.bazel.build/github.com/bazelbuild/bazel-skylib/releases/download/1.0.3/bazel-skylib-1.0.3.tar.gz",
    ],
    sha256 = "1c531376ac7e5a180e0237938a2536de0c54d93f5c278634818e0efc952dd56c",
)

load("//tools/openocd:openocd_repository.bzl", "openocd_deps")

openocd_deps()

load("@bazel_skylib//:workspace.bzl", "bazel_skylib_workspace")

bazel_skylib_workspace()

load("//toolchains/compilers/gcc_arm_none_eabi:gcc_arm_none_repository.bzl", "gcc_arm_none_compiler")

gcc_arm_none_compiler()

load("//platforms:execution_platforms.bzl", "register_platforms")

register_platforms()

load("//toolchains/gcc_arm_none_eabi:gcc_arm_none_toolchain.bzl", "register_gcc_arm_none_toolchain")

register_gcc_arm_none_toolchain()

git_repository(
    name = "io_bazel_stardoc",
    remote = "https://github.com/bazelbuild/stardoc.git",
    tag = "0.4.0",
)

load("@io_bazel_stardoc//:setup.bzl", "stardoc_repositories")

stardoc_repositories()

http_archive(
    name = "com_github_wjwwood_serial",
    sha256 = "55381e43ddf0920c955994fa5f519f95e867ea4e4280a2cf55c4dfd3266b19c0",
    strip_prefix = "serial-8068164faa1a48e18deaf6a15db7950a09b30b9e",
    urls = ["https://github.com/silvergasp/serial/archive/8068164faa1a48e18deaf6a15db7950a09b30b9e.zip"],
)

http_archive(
    name = "com_github_jarro_cxxopts",
    sha256 = "fbee4be13a388dd4164865d707a7062a3051a8c83c4f30c56ef9616bdf202210",
    strip_prefix = "cxxopts-5e323d648e50b43fd430fb324c632dafd73f7add",
    urls = ["https://github.com/silvergasp/cxxopts/archive/5e323d648e50b43fd430fb324c632dafd73f7add.zip"],
)

# Change master to the git tag you want.
http_archive(
    name = "com_grail_bazel_toolchain",
    sha256 = "14610f3b6a7b41600bec9168461101fe7b63f095c8724d965a64e51f49a980d5",
    strip_prefix = "bazel-toolchain-5d6406ee54b3aa04139f30769b4e94538a80bc52",
    urls = ["https://github.com/grailbio/bazel-toolchain/archive/5d6406ee54b3aa04139f30769b4e94538a80bc52.zip"],
)

load("@com_grail_bazel_toolchain//toolchain:deps.bzl", "bazel_toolchain_dependencies")

bazel_toolchain_dependencies()

# This sysroot is used by github.com/vsco/bazel-toolchains.
http_archive(
    name = "org_chromium_sysroot_linux_x64",
    build_file_content = """
filegroup(
  name = "sysroot",
  srcs = glob(["*/**"]),
  visibility = ["//visibility:public"],
)
""",
    sha256 = "84656a6df544ecef62169cfe3ab6e41bb4346a62d3ba2a045dc5a0a2ecea94a3",
    urls = ["https://commondatastorage.googleapis.com/chrome-linux-sysroot/toolchain/2202c161310ffde63729f29d27fe7bb24a0bc540/debian_stretch_amd64_sysroot.tar.xz"],
)

load("@com_grail_bazel_toolchain//toolchain:rules.bzl", "llvm_toolchain")

llvm_toolchain(
    name = "llvm_toolchain",
    llvm_version = "9.0.0",
    sysroot = {
        "linux": "@org_chromium_sysroot_linux_x64//:sysroot",
    },
)

load("@llvm_toolchain//:toolchains.bzl", "llvm_register_toolchains")

llvm_register_toolchains()
