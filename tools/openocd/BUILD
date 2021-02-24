load("@io_bazel_stardoc//stardoc:stardoc.bzl", "stardoc")
load(":defs.bzl", "openocd_debug_server", "openocd_execution_wrapper", "openocd_flash")

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

openocd_execution_wrapper(
    name = "test_wrapper",
    device_configs = [
        "target/stm32h7x_dual_bank.cfg",
    ],
    interface_configs = [
        "interface/stlink.cfg",
    ],
    transport = "hla_swd",
)

openocd_debug_server(
    name = "debug_server",
    device_configs = [
        "target/stm32h7x_dual_bank.cfg",
    ],
    interface_configs = [
        "interface/stlink.cfg",
    ],
    transport = "hla_swd",
)

openocd_flash(
    name = "flasher",
    device_configs = [
        "target/stm32h7x_dual_bank.cfg",
    ],
    image = "//toolchains/compilation_tests:compilation_test_cc",
    interface_configs = [
        "interface/stlink.cfg",
    ],
    transport = "hla_swd",
)
