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
    )

    if not native.existing_rule("rules_cc"):
        git_repository(
            name = "rules_cc",
            commit = "a636005ba28c0344da5110bd8532184c74b6ffdf",
            remote = "https://github.com/bazelbuild/rules_cc.git",
        )
    if not native.existing_rule("bazel_skylib"):
        http_archive(
            name = "bazel_skylib",
            sha256 = "97e70364e9249702246c0e9444bccdc4b847bed1eb03c5a3ece4f83dfe6abc44",
            urls = [
                "https://mirror.bazel.build/github.com/bazelbuild/bazel-skylib/releases/download/1.0.2/bazel-skylib-1.0.2.tar.gz",
                "https://github.com/bazelbuild/bazel-skylib/releases/download/1.0.2/bazel-skylib-1.0.2.tar.gz",
            ],
        )
    if not native.existing_rule("com_github_wjwwood_serial"):
        http_archive(
            name = "com_github_wjwwood_serial",
            sha256 = "9f8e80d3f3776862468bafaa0773e3d281f4f980dcbdfc72ddb0e9f619a6544f",
            strip_prefix = "serial-abba176643a7a141bc6d3d81ce8f304363830af6",
            urls = ["https://github.com/silvergasp/serial/archive/abba176643a7a141bc6d3d81ce8f304363830af6.zip"],
        )
    if not native.existing_rule("com_github_jarro_cxxopts"):
        http_archive(
            name = "com_github_jarro_cxxopts",
            sha256 = "fbee4be13a388dd4164865d707a7062a3051a8c83c4f30c56ef9616bdf202210",
            strip_prefix = "cxxopts-5e323d648e50b43fd430fb324c632dafd73f7add",
            urls = ["https://github.com/silvergasp/cxxopts/archive/5e323d648e50b43fd430fb324c632dafd73f7add.zip"],
        )
