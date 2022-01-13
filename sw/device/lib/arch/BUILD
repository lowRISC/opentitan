package(default_visibility = ["//visibility:public"])

load("//rules:opentitan.bzl", "OPENTITAN_CPU")

cc_library(
    name = "device",
    hdrs = ["device.h"],
)

cc_library(
    name = "fpga_nexysvideo",
    srcs = ["device_fpga_nexysvideo.c"],
    deps = [":device"],
)

cc_library(
    name = "fpga_cw310",
    srcs = ["device_fpga_cw310.c"],
    deps = [":device"],
)

cc_library(
    name = "sim_dv",
    srcs = ["device_sim_dv.c"],
    deps = [":device"],
)

cc_library(
    name = "sim_verilator",
    srcs = ["device_sim_verilator.c"],
    deps = [":device"],
)
