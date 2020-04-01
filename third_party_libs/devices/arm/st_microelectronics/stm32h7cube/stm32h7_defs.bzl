load("@rules_cc//cc:defs.bzl", "cc_library")

INCLUDE_DIRECTORIES = [
    "Drivers/CMSIS/Core_A/Include",
    "Drivers/CMSIS/Core/Include",
    "Drivers/CMSIS/Device/ST/STM32H7xx/Include",
    "Drivers/CMSIS/DSP/Include",
    "Drivers/CMSIS/Include",
    "Drivers/CMSIS/NN/Include",
    "Drivers/CMSIS/RTOS2/Include",
    "Drivers/STM32H7xx_HAL_Driver/Inc",
    "Drivers/STM32H7xx_HAL_Driver/Inc/Legacy",
    "Middlewares/ST/STM32_Network_Library/Includes",
    "Middlewares/ST/STM32_USB_Device_Library/Class/AUDIO/Inc",
    "Middlewares/ST/STM32_USB_Device_Library/Class/CDC/Inc",
    "Middlewares/ST/STM32_USB_Device_Library/Class/CustomHID/Inc",
    "Middlewares/ST/STM32_USB_Device_Library/Class/DFU/Inc",
    "Middlewares/ST/STM32_USB_Device_Library/Class/HID/Inc",
    "Middlewares/ST/STM32_USB_Device_Library/Class/MSC/Inc",
    "Middlewares/ST/STM32_USB_Device_Library/Core/Inc",
    "Middlewares/ST/STM32_USB_Host_Library/Class/AUDIO/Inc",
    "Middlewares/ST/STM32_USB_Host_Library/Class/CDC/Inc",
    "Middlewares/ST/STM32_USB_Host_Library/Class/HID/Inc",
    "Middlewares/ST/STM32_USB_Host_Library/Class/MSC/Inc",
    "Middlewares/ST/STM32_USB_Host_Library/Class/MTP/Inc",
    "Middlewares/ST/STM32_USB_Host_Library/Core/Inc",
    "Middlewares/Third_Party/FatFs/src",
    "Middlewares/Third_Party/FatFs/src/drivers",
    "Middlewares/Third_Party/LwIP/system/arch",
    "Middlewares/Third_Party/mbedTLS/include/mbedtls",
    "Middlewares/Third_Party/mbedTLS/include",
]

CMSIS_GLOB_EXCLUSIONS = [
    "**/IAR/**",
    "Drivers/CMSIS/Core_A/**",
    "Drivers/CMSIS/NN/**",
    "Drivers/CMSIS/DSP/**",
    "Drivers/CMSIS/RTOS2/**",
]

STM32_DEFINES = {
    "stm32h743xx": [
        "USE_HAL_DRIVER",
        "STM32H743xx",
    ],
    "stm32h753xx": [
        "USE_HAL_DRIVER",
        "STM32H753xx",
    ],
    "stm32h750xx": [
        "USE_HAL_DRIVER",
        "STM32H750xx",
    ],
    "stm32h742xx": [
        "USE_HAL_DRIVER",
        "STM32H742xx",
    ],
    "stm32h745xx_core_m4": [
        "USE_HAL_DRIVER",
        "STM32H745xx",
        "CORE_CM4",
    ],
    "stm32h745xx_core_m7": [
        "USE_HAL_DRIVER",
        "STM32H745xx",
        "CORE_CM7",
    ],
    "stm32h755xx_core_m4": [
        "USE_HAL_DRIVER",
        "STM32H755xx",
        "CORE_CM4",
    ],
    "stm32h755xx_core_m7": [
        "USE_HAL_DRIVER",
        "STM32H755xx",
        "CORE_CM7",
    ],
    "stm32h747xx_core_m4": [
        "USE_HAL_DRIVER",
        "STM32H747xx",
        "CORE_CM4",
    ],
    "stm32h747xx_core_m7": [
        "USE_HAL_DRIVER",
        "STM32H747xx",
        "CORE_CM7",
    ],
    "stm32h757xx_core_m4": [
        "USE_HAL_DRIVER",
        "STM32H757xx",
        "CORE_CM4",
    ],
    "stm32h757xx_core_m7": [
        "USE_HAL_DRIVER",
        "STM32H757xx",
        "CORE_CM7",
    ],
    "stm32h7b0xx": [
        "USE_HAL_DRIVER",
        "STM32H7B0xx",
    ],
    "stm32h7b0xxq": [
        "USE_HAL_DRIVER",
        "STM32H7B0xxQ",
    ],
    "stm32h7a3xx": [
        "USE_HAL_DRIVER",
        "STM32H7A3xx",
    ],
    "stm32h7b3xx": [
        "USE_HAL_DRIVER",
        "STM32H7B3xx",
    ],
    "stm32h7a3xxq": [
        "USE_HAL_DRIVER",
        "STM32H7A3xxQ",
    ],
    "stm32h7b3xxq": [
        "USE_HAL_DRIVER",
        "STM32H7B3xxQ",
    ],
}

def stm32h7_startup_file(device):
    return "@stm32h7cube//Drivers/CMSIS/Device/ST/STM32H7xx/Source/Templates/gcc/startup_" + device + ".s"

def stm32h7_project(name, config):
    """stm32h7xx_project initialises a project that can be used with stm32h7cube repository

    This macro may not be idiomatic for bazel libraries. This is due to the need to provide user defined config libraries for each project. This library is designed to be used inside the stm32h7xx_repository and automatically generates a set of targets per project. This allows you to have multiple projects defined in the same workspace with differing configs. This macro will produce the following targets, '{name}_hal_driver', '{name}_stm32_network_library', '{name}_stm32_usb_device_library', '{name}_stm32_usb_host_library', '{name}_st_middlewares', '{name}_fatfs', '{name}_mbed_tls', '{name}__third_party_middlewares'

    Args:
        name: The name of your project
        config: The label for your cc_library providing all the config files relevant for cubemx initialisation. Note that this label must be the full label of your target in your repository. i.e. the target '@my_workspace_name//:config' is ok but '//:config' is not.
"""
    include_directories = INCLUDE_DIRECTORIES
    defines = []
    glob_excludes = ["**/*template.c"]

    cc_library(
        name = name + "_hal_driver",
        srcs = native.glob(["Drivers/STM32H7xx_HAL_Driver/**/*.c"], exclude = glob_excludes),
        hdrs = native.glob(["**/*.h"]),
        copts = ["-include stdint.h"],
        defines = defines,
        includes = include_directories,
        deps = [config],
        tags = ["manual"],
        alwayslink = True,
    )

    cc_library(
        name = name + "_stm32_network_library",
        srcs = native.glob(["Middlewares/ST/STM32_Netowrk_Library/**/*.c"], exclude = glob_excludes),
        hdrs = native.glob(["**/*.h"]),
        defines = defines,
        includes = include_directories,
        deps = [config],
        tags = ["manual"],
        alwayslink = True,
    )

    cc_library(
        name = name + "_stm32_usb_device_library",
        srcs = native.glob(["MiddleWares/ST/STM32_USB_Device_Library/**/*.c"], exclude = glob_excludes),
        hdrs = native.glob(["**/*.h"]),
        defines = defines,
        includes = include_directories,
        deps = [config],
        tags = ["manual"],
        alwayslink = True,
    )

    cc_library(
        name = name + "_stm32_usb_host_library",
        srcs = native.glob(["MiddleWares/ST/STM32_USB_Host_Library/**/*.c"], exclude = glob_excludes),
        hdrs = native.glob(["**/*.h"]),
        defines = defines,
        includes = include_directories,
        deps = [config],
        tags = ["manual"],
        alwayslink = True,
    )

    cc_library(
        name = name + "_st_middlewares",
        deps = [
            ":" + name + "_stm32_network_library",
            ":" + name + "_stm32_usb_device_library",
            ":" + name + "_stm32_usb_host_library",
        ],
        tags = ["manual"],
        alwayslink = True,
    )

    cc_library(
        name = name + "_fatfs",
        srcs = native.glob(["Middlewares/Third_Party/FatFs/src/*.c"], exclude = glob_excludes),
        hdrs = native.glob(["Middlewares/Third_Party/FatFs/src/*.h"]),
        includes = include_directories,
        deps = [config],
        tags = ["manual"],
        alwayslink = True,
    )

    cc_library(
        name = name + "_mbed_tls",
        srcs = native.glob(
            ["Middlewares/Third_Party/mbedTLS/library/*.c"],
            exclude = glob_excludes,
        ),
        hdrs = native.glob(["Middlewares/Third_Party/mbedTLS/include/mbedtls/*.h"]),
        copts = [
            '-DMBEDTLS_CONFIG_FILE=\\"mbedtls_conf.h\\"',
        ],
        includes = include_directories,
        deps = [config],
        tags = ["manual"],
        alwayslink = True,
    )

    cc_library(
        name = name + "_third_party_middlewares",
        deps = [
            ":" + name + "_fatfs",
            ":" + name + "_mbed_tls",
        ],
        tags = ["manual"],
        alwayslink = True,
    )
