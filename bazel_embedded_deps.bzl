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
