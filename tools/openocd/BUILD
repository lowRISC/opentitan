load("@io_bazel_stardoc//stardoc:stardoc.bzl", "stardoc")

stardoc(
    name = "openocd_repository_docs",
    out = "openocd_repository.md",
    input = "openocd_repository.bzl",
    symbol_names = ["openocd_deps"],
)

stardoc(
    name = "openocd_docs",
    out = "openocd.md",
    input = "defs.bzl",
)
