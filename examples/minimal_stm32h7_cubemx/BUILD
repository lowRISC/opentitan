load("@stm32h7cube//:stm32h7_defs.bzl", "STM32_DEFINES")

cc_library(
    name = "minimal_cubemx_project_config",
    hdrs = [
        "Inc/main.h",
        "Inc/stm32h7xx_hal_conf.h",
    ],
    defines = STM32_DEFINES["stm32h743xx"],
    includes = ["Inc"],
    visibility = ["//visibility:public"],
    alwayslink = True,
)

cc_binary(
    name = "main",
    srcs = glob(["Src/*.c"]) + ["Inc/stm32h7xx_it.h"],
    additional_linker_inputs = ["STM32H743XIHx_FLASH.ld"],
    defines = STM32_DEFINES["stm32h743xx"],
    includes = ["Inc"],
    linkopts = ["-T $(location :STM32H743XIHx_FLASH.ld)"],
    deps = [
        "@stm32h7cube//:minimal_hal_driver",
        "@stm32h7cube//:startup_stm32h743xx",
    ],
)
