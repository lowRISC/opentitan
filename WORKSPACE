load("@bazel_tools//tools/build_defs/repo:git.bzl", "git_repository")
load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

git_repository(
    name = "bazel_embedded",
    commit = "f7299c20ea6182e164adabc336ba2a7c0d8caa71",
    remote = "https://github.com/lowRISC/bazel-embedded.git",
    shallow_since = "1628013051 +0000",
)

load("@bazel_embedded//:bazel_embedded_deps.bzl", "bazel_embedded_deps")

bazel_embedded_deps()

load("@bazel_embedded//platforms:execution_platforms.bzl", "register_platforms")

register_platforms()

load(
    "@bazel_embedded//toolchains/compilers/lowrisc_toolchain_rv32imc:lowrisc_toolchain_rv32imc_repository.bzl",
    "lowrisc_toolchain_rv32imc_compiler",
)

lowrisc_toolchain_rv32imc_compiler()

load(
    "@bazel_embedded//toolchains/lowrisc_toolchain_rv32imc:lowrisc_toolchain_rv32imc.bzl",
    "register_lowrisc_toolchain_rv32imc_toolchain",
)

register_lowrisc_toolchain_rv32imc_toolchain()

# We have a 'vendored' copy of the googletest repo in our repository.
# In the future, we may want to change this to a git repo or http archive.
local_repository(
    name = "googletest",
    path = "sw/vendor/google_googletest",
)

# Abseil is required by googletest.
http_archive(
    name = "com_google_absl",
    strip_prefix = "abseil-cpp-master",
    urls = ["https://github.com/abseil/abseil-cpp/archive/master.zip"],
)
