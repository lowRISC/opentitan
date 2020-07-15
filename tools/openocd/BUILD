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

load(":defs.bzl", "openocd_execution_wrapper")

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
