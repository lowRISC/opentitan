""" Fetch remote third party dependencies """

load("@bazel_tools//tools/build_defs/repo:git.bzl", "git_repository")
load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

def bazel_embedded_deps():
    """ bazel_embedded_deps downloads and setups up the required thirdy party dependencies """

    #if not native.existing_rule("platforms"):
    # TODO: add the above if statement back when cortex-m constraint values are added to mainline bazel
    git_repository(
        name = "platforms",
        remote = "https://github.com/curtin-space/platforms.git",
        commit = "a9fb73e46ab4a7558d53d65ed8e608724f07d4cc",
        shallow_since = "1585009972 +0800"
    )

    if not native.existing_rule("rules_cc"):
        git_repository(
            name = "rules_cc",
            commit = "a636005ba28c0344da5110bd8532184c74b6ffdf",
            remote = "https://github.com/bazelbuild/rules_cc.git",
            shallow_since = "1583316607 -0800",
        )
    if not native.existing_rule("bazel_skylib"):
        http_archive(
            name = "bazel_skylib",
            urls = [
                "https://github.com/bazelbuild/bazel-skylib/releases/download/1.0.3/bazel-skylib-1.0.3.tar.gz",
                "https://mirror.bazel.build/github.com/bazelbuild/bazel-skylib/releases/download/1.0.3/bazel-skylib-1.0.3.tar.gz",
            ],
            sha256 = "1c531376ac7e5a180e0237938a2536de0c54d93f5c278634818e0efc952dd56c",
        )
    if not native.existing_rule("com_github_wjwwood_serial"):
        http_archive(
            name = "com_github_wjwwood_serial",
            sha256 = "55381e43ddf0920c955994fa5f519f95e867ea4e4280a2cf55c4dfd3266b19c0",
            strip_prefix = "serial-8068164faa1a48e18deaf6a15db7950a09b30b9e",
            urls = ["https://github.com/silvergasp/serial/archive/8068164faa1a48e18deaf6a15db7950a09b30b9e.zip"],
        )
    if not native.existing_rule("com_github_jarro_cxxopts"):
        http_archive(
            name = "com_github_jarro_cxxopts",
            sha256 = "fbee4be13a388dd4164865d707a7062a3051a8c83c4f30c56ef9616bdf202210",
            strip_prefix = "cxxopts-5e323d648e50b43fd430fb324c632dafd73f7add",
            urls = ["https://github.com/silvergasp/cxxopts/archive/5e323d648e50b43fd430fb324c632dafd73f7add.zip"],
        )
