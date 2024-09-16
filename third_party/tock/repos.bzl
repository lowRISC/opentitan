# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@//rules:repo.bzl", "bare_repository", "http_archive_or_local")
load("@//rules:rust.bzl", "crate_build")
load("@python3//:defs.bzl", "interpreter")
load("@rules_python//python:pip.bzl", "pip_install")

# Exports the kernel_layout.ld file so it can be used in opentitan rules.
_KERNEL_LAYOUT = """
package(default_visibility = ["//visibility:public"])

filegroup(
    name = "kernel_layout",
    srcs = ["kernel_layout.ld"],
)
"""

# Exports the libtock_layout.ld file so it can be used in opentitan rules.
_LIBTOCK_LAYOUT = """
filegroup(
    name = "layout",
    srcs = ["libtock_layout.ld"],
)
"""

# Exports the earlgrey-cw310 crate sources so we can build a local copy
# of the upstream kernel.
_EARLGREY_CW310_BUILD = """
package(default_visibility = ["//visibility:public"])

filegroup(
    name = "kernel_srcs",
    srcs = glob(["**/*.rs"]),
)
"""

def tock_repos(tock = None, libtock = None, elf2tab = None):
    bare_repository(
        name = "tock",
        local = tock,
        strip_prefix = "tock-5a65d681489d30a4b88b5d1a7d2a0e8273cbf027",
        url = "https://github.com/tock/tock/archive/5a65d681489d30a4b88b5d1a7d2a0e8273cbf027.tar.gz",
        sha256 = "38f3efcaaa6c4e22a7c4fa8f2befa651ec1a9f730089434696ad781f6b479c79",
        additional_files_content = {
            "BUILD": """exports_files(glob(["**"]))""",
            "arch/riscv/BUILD": crate_build(
                name = "riscv",
                deps = [
                    "//kernel",
                    "//libraries/tock-register-interface:tock-registers",
                    "//libraries/riscv-csr",
                ],
            ),
            "arch/rv32i/BUILD": crate_build(
                name = "rv32i",
                deps = [
                    "//arch/riscv",
                    "//kernel",
                    "//libraries/tock-register-interface:tock-registers",
                    "//libraries/riscv-csr",
                ],
            ),
            "boards/BUILD": _KERNEL_LAYOUT,
            "boards/components/BUILD": crate_build(
                name = "components",
                deps = [
                    "//kernel",
                    "//capsules/core:capsules-core",
                    "//capsules/extra:capsules-extra",
                    "//capsules/system:capsules-system",
                ],
            ),
            "boards/opentitan/earlgrey-cw310/BUILD": _EARLGREY_CW310_BUILD,
            "capsules/aes_gcm/BUILD": crate_build(
                name = "capsules-aes-gcm",
                deps = [
                    "//kernel",
                    "//libraries/enum_primitive",
                    "//libraries/tickv",
                    "@tock_index//:ghash",
                ],
            ),
            "capsules/core/BUILD": crate_build(
                name = "capsules-core",
                deps = [
                    "//kernel",
                    "//libraries/enum_primitive",
                    "//libraries/tickv",
                ],
            ),
            "capsules/extra/BUILD": crate_build(
                name = "capsules-extra",
                deps = [
                    "//kernel",
                    "//libraries/enum_primitive",
                    "//libraries/tickv",
                    "//capsules/core:capsules-core",
                ],
            ),
            "capsules/system/BUILD": crate_build(
                name = "capsules-system",
                deps = [
                    "//kernel",
                    "//libraries/tock-tbf",
                ],
            ),
            "chips/earlgrey/BUILD": crate_build(
                name = "earlgrey",
                deps = [
                    "//chips/lowrisc",
                    "//arch/rv32i",
                    "//kernel",
                ],
            ),
            "chips/lowrisc/BUILD": crate_build(
                name = "lowrisc",
                deps = [
                    "//arch/rv32i",
                    "//kernel",
                ],
            ),
            "libraries/enum_primitive/BUILD": crate_build(
                name = "enum_primitive",
            ),
            "libraries/riscv-csr/BUILD": crate_build(
                name = "riscv-csr",
                deps = [
                    "//libraries/tock-register-interface:tock-registers",
                ],
            ),
            "libraries/tickv/BUILD": crate_build(
                name = "tickv",
            ),
            "libraries/tock-cells/BUILD": crate_build(
                name = "tock-cells",
            ),
            "libraries/tock-tbf/BUILD": crate_build(
                name = "tock-tbf",
            ),
            "libraries/tock-register-interface/BUILD": crate_build(
                name = "tock-registers",
                crate_features = [
                    "default",
                    "register_types",
                ],
            ),
            "kernel/BUILD": crate_build(
                name = "kernel",
                deps = [
                    "//libraries/tock-register-interface:tock-registers",
                    "//libraries/tock-cells",
                    "//libraries/tock-tbf",
                ],
            ),
        },
    )

    bare_repository(
        name = "libtock",
        local = libtock,
        strip_prefix = "libtock-rs-f4bd533a37a65c5eb15d1488be61b2d00872dfc5",
        url = "https://github.com/tock/libtock-rs/archive/f4bd533a37a65c5eb15d1488be61b2d00872dfc5.tar.gz",
        sha256 = "3169321d465fe54403cf524287efd98a514f6a9ad11a3b792e0ead2b764accf0",
        additional_files_content = {
            "BUILD": crate_build(
                name = "libtock",
                deps = [
                    "//apis/interface/buttons",
                    "//apis/interface/buzzer",
                    "//apis/interface/console",
                    "//apis/interface/leds",
                    "//apis/kernel/low_level_debug",
                    "//apis/peripherals/adc",
                    "//apis/peripherals/alarm",
                    "//apis/peripherals/gpio",
                    "//apis/peripherals/i2c_master",
                    "//apis/peripherals/i2c_master_slave",
                    "//apis/peripherals/rng",
                    "//apis/peripherals/spi_controller",
                    "//apis/sensors/air_quality",
                    "//apis/sensors/ambient_light",
                    "//apis/sensors/ninedof",
                    "//apis/sensors/proximity",
                    "//apis/sensors/sound_pressure",
                    "//apis/sensors/temperature",
                    "//apis/storage/key_value",
                    "//panic_handlers/debug_panic",
                    "//panic_handlers/small_panic",
                    "//platform",
                    "//runtime",
                ],
            ),
            "apis/interface/buttons/BUILD": crate_build(
                name = "buttons",
                crate_name = "libtock_{name}",
                deps = ["//platform"],
            ),
            "apis/interface/buzzer/BUILD": crate_build(
                name = "buzzer",
                crate_name = "libtock_{name}",
                deps = ["//platform"],
            ),
            "apis/interface/console/BUILD": crate_build(
                name = "console",
                crate_name = "libtock_{name}",
                deps = ["//platform"],
            ),
            "apis/interface/leds/BUILD": crate_build(
                name = "leds",
                crate_name = "libtock_{name}",
                deps = ["//platform"],
            ),
            "apis/kernel/low_level_debug/BUILD": crate_build(
                name = "low_level_debug",
                crate_name = "libtock_{name}",
                deps = ["//platform"],
            ),
            "apis/peripherals/adc/BUILD": crate_build(
                name = "adc",
                crate_name = "libtock_{name}",
                deps = ["//platform"],
            ),
            "apis/peripherals/alarm/BUILD": crate_build(
                name = "alarm",
                crate_name = "libtock_{name}",
                deps = ["//platform"],
            ),
            "apis/peripherals/gpio/BUILD": crate_build(
                name = "gpio",
                crate_name = "libtock_{name}",
                deps = ["//platform"],
            ),
            "apis/peripherals/i2c_master/BUILD": crate_build(
                name = "i2c_master",
                crate_name = "libtock_{name}",
                deps = ["//platform"],
            ),
            "apis/peripherals/i2c_master_slave/BUILD": crate_build(
                name = "i2c_master_slave",
                crate_name = "libtock_{name}",
                deps = ["//platform"],
            ),
            "apis/peripherals/rng/BUILD": crate_build(
                name = "rng",
                crate_name = "libtock_{name}",
                deps = ["//platform"],
            ),
            "apis/peripherals/spi_controller/BUILD": crate_build(
                name = "spi_controller",
                crate_name = "libtock_{name}",
                deps = ["//platform"],
            ),
            "apis/sensors/air_quality/BUILD": crate_build(
                name = "air_quality",
                crate_name = "libtock_{name}",
                deps = ["//platform"],
            ),
            "apis/sensors/ambient_light/BUILD": crate_build(
                name = "ambient_light",
                crate_name = "libtock_{name}",
                deps = ["//platform"],
            ),
            "apis/sensors/ninedof/BUILD": crate_build(
                name = "ninedof",
                crate_name = "libtock_{name}",
                deps = [
                    "//platform",
                    "@tock_index//:libm",
                ],
            ),
            "apis/sensors/proximity/BUILD": crate_build(
                name = "proximity",
                crate_name = "libtock_{name}",
                deps = ["//platform"],
            ),
            "apis/sensors/sound_pressure/BUILD": crate_build(
                name = "sound_pressure",
                crate_name = "libtock_{name}",
                deps = ["//platform"],
            ),
            "apis/sensors/temperature/BUILD": crate_build(
                name = "temperature",
                crate_name = "libtock_{name}",
                deps = ["//platform"],
            ),
            "apis/storage/key_value/BUILD": crate_build(
                name = "key_value",
                crate_name = "libtock_{name}",
                deps = ["//platform"],
            ),
            "build_scripts/BUILD": crate_build(
                name = "build_scripts",
                crate_name = "libtock_{name}",
                additional_build_file_content = _LIBTOCK_LAYOUT,
            ),
            "panic_handlers/debug_panic/BUILD": crate_build(
                name = "debug_panic",
                crate_name = "libtock_{name}",
                deps = [
                    "//apis/interface/console",
                    "//apis/kernel/low_level_debug",
                    "//platform",
                    "//runtime",
                ],
            ),
            "panic_handlers/small_panic/BUILD": crate_build(
                name = "small_panic",
                crate_name = "libtock_{name}",
                deps = [
                    "//apis/kernel/low_level_debug",
                    "//platform",
                    "//runtime",
                ],
            ),
            "platform/BUILD": crate_build(
                name = "platform",
                crate_name = "libtock_{name}",
            ),
            "runtime/BUILD": crate_build(
                name = "runtime",
                crate_name = "libtock_{name}",
                deps = [
                    "//platform",
                ],
            ),
        },
    )

    http_archive_or_local(
        name = "elf2tab",
        local = elf2tab,
        url = "https://github.com/tock/elf2tab/archive/2f0e2f0ef01e37799850d1b12f48b93a0b32a203.tar.gz",
        sha256 = "b8b2ec7d8b9d052667d34190f98a0f5e69a0ba93ce69f00f2fdda7b5e241b963",
        strip_prefix = "elf2tab-2f0e2f0ef01e37799850d1b12f48b93a0b32a203",
        build_file = Label("//third_party/tock:BUILD.elf2tab.bazel"),
    )

    pip_install(
        name = "tockloader_deps",
        python_interpreter_target = interpreter,
        requirements = "//:third_party/tock/tockloader_requirements.txt",
    )
