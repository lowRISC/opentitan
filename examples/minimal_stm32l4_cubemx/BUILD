load("@stm32l4cube//:stm32l4_defs.bzl", "STM32_DEFINES")

cc_library(
    name = "minimal_cubemx_project_config",
    hdrs = [
        "Inc/main.h",
        "Inc/stm32l4xx_hal_conf.h",
    ],
    defines = STM32_DEFINES["stm32l43"],
    includes = ["Inc"],
    visibility = ["//visibility:public"],
    alwayslink = True,
)
