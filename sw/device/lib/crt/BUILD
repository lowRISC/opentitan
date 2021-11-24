package(default_visibility = ["//visibility:public"])

load("//rules:opentitan.bzl", "OPENTITAN_CPU")

cc_library(
    name = "crt",
    srcs = ["crt.S"],
    target_compatible_with = [OPENTITAN_CPU],
)
