package(default_visibility = ["//visibility:public"])

platform(
    name = "cortex_m",
    constraint_values = [
        "@bazel_embedded//constraints/fpu:none",
        "@platforms//cpu:armv6-m",
    ],
)

platform(
    name = "cortex_m0",
    exec_properties = {
        "EXECUTOR": "cortex_m",
    },
    parents = [":cortex_m"],
)

platform(
    name = "cortex_m1",
    exec_properties = {
        "EXECUTOR": "cortex_m1",
    },
    parents = [":cortex_m"],
)

platform(
    name = "cortex_m3",
    constraint_values = [
        "@platforms//cpu:armv7-m",
    ],
    exec_properties = {
        "EXECUTOR": "cortex_m3",
    },
    parents = [":cortex_m"],
)

platform(
    name = "cortex_m4",
    constraint_values = [
        "@platforms//cpu:armv7e-m",
    ],
    exec_properties = {
        "EXECUTOR": "cortex_m4",
    },
    parents = [":cortex_m3"],
)

platform(
    name = "cortex_m4_fpu",
    constraint_values = [
        "@bazel_embedded//constraints/fpu:fpv4-sp-d16",
    ],
    exec_properties = {
        "EXECUTOR": "cortex_m4_fpu",
    },
    parents = [":cortex_m4"],
)

platform(
    name = "cortex_m7",
    exec_properties = {
        "EXECUTOR": "cortex_m7",
    },
    parents = [":cortex_m4"],
)

platform(
    name = "cortex_m7_fpu",
    constraint_values = [
        "@platforms//cpu:armv7e-m",
        "@bazel_embedded//constraints/fpu:fpv5-d16",
    ],
    exec_properties = {
        "EXECUTOR": "cortex_m7_fpu",
    },
    parents = [":cortex_m"],
)

platform(
    name = "opentitan_rv32imc",
    constraint_values = [
        "@bazel_embedded//constraints/fpu:none",
        "@bazel_embedded//constraints/cpu:riscv32",
        # TODO(cfrantz): change to this after upstreaming cpu constraints.
        # See https://github.com/bazelbuild/platforms/pull/30.
    ],
)

platform(
    name = "stm32f2xx",
    parents = [":cortex_m3"],
)

platform(
    name = "stm32f3xx",
    parents = [":cortex_m4_fpu"],
)

platform(
    name = "stm32f4xx",
    parents = [":cortex_m4"],
)

platform(
    name = "stm32f7xx",
    parents = [":cortex_m7_fpu"],
)

platform(
    name = "stm32g4xx",
    parents = [":cortex_m4_fpu"],
)

platform(
    name = "stm32h7xx",
    parents = [":cortex_m7_fpu"],
)
