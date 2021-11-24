package(default_visibility = ["//visibility:public"])

cc_library(
    name = "demos",
    srcs = ["demos.c"],
    hdrs = ["demos.h"],
    deps = [
        "//sw/device/lib/arch:device",
        "//sw/device/lib/dif:gpio",
        "//sw/device/lib/dif:spi_device",
        "//sw/device/lib/dif:uart",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing",
    ],
)
