""" Fetch remote third party dependencies """

load("@bazel_tools//tools/build_defs/repo:git.bzl", "git_repository")

def bazel_embedded_deps():
""" bazel_embedded_deps downloads and setups up the required thirdy party dependencies """
    #if not native.existing_rule("platforms"):
    # TODO: add the above if statement back when cortex-m constraint values are added to mainline bazel
    git_repository(
        name = "platforms",
        remote = "https://github.com/curtin-space/platforms.git",
        commit = "a9fb73e46ab4a7558d53d65ed8e608724f07d4cc",
    )
