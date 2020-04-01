load("@rules_cc//cc:defs.bzl", "cc_library")

INCLUDE_DIRECTORIES = [
    "Drivers/CMSIS/Core_A/Include",
    "Drivers/CMSIS/Core/Include",
    "Drivers/CMSIS/Device/ST/STM32L4xx/Include",
    "Drivers/CMSIS/DSP/Include",
    "Drivers/CMSIS/Include",
    "Drivers/CMSIS/NN/Include",
    "Drivers/CMSIS/RTOS2/Include",
    "Drivers/STM32L4xx_HAL_Driver/Inc",
    "Drivers/STM32L4xx_HAL_Driver/Inc/Legacy",
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
]

CMSIS_GLOB_EXCLUSIONS = [
    "**/IAR/**",
    "Drivers/CMSIS/Core_A/**",
    "Drivers/CMSIS/NN/**",
    "Drivers/CMSIS/DSP/**",
    "Drivers/CMSIS/RTOS2/**",
]

STM32_DEFINES = {
    "stm32l4r5xx": ["STM32L4R5xx", "USE_HAL_DRIVER"],
    "stm32l4r9xx": ["STM32L4R9xx", "USE_HAL_DRIVER"],
    "stm32l4s5xx": ["STM32L4S5xx", "USE_HAL_DRIVER"],
    "stm32l4s7xx": ["STM32L4S7xx", "USE_HAL_DRIVER"],
    "stm32l432xx": ["STM32L432xx", "USE_HAL_DRIVER"],
}

def stm32h7_startup_file(device):
    return "@stm32l4cube//Drivers/CMSIS/Device/ST/STM32H7xx/Source/Templates/gcc/startup_" + device + ".s"

def stm32l4_project(name, config):
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
        srcs = native.glob(["Drivers/STM32L4xx_HAL_Driver/**/*.c"], exclude = glob_excludes),
        hdrs = native.glob(["**/*.h"]),
        copts = ["-include stdint.h"],
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
        name = name + "_third_party_middlewares",
        deps = [
            ":" + name + "_fatfs",
        ],
        tags = ["manual"],
        alwayslink = True,
    )
