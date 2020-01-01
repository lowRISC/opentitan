platform(
    name = "cortex_m",
    constraint_values = [
        "@platforms//os:none",
        "//constraints/fpu:none",
        "//constraints/cpu:armv6-m",
    ],
)

platform(
    name = "cortex_m0",
    parents = [":cortex_m"],
)

platform(
    name = "cortex_m1",
    parents = [":cortex_m"],
)

platform(
    name = "cortex_m3",
    constraint_values = [
        "//constraints/cpu:armv7-m",
    ],
    parents = [":cortex_m"],
)

platform(
    name = "cortex_m4",
    parents = [":cortex_m3"],
)

platform(
    name = "cortex_m4_fpu",
    constraint_values = [
        "//constraints/fpu:fpv4-sp-d16",
    ],
    parents = [":cortex_m4"],
)

platform(
    name = "cortex_m7",
    constraint_values = [
        "//constraints/cpu:armv7e-m",
    ],
    parents = [":cortex_m"],
)

platform(
    name = "cortex_m7_fpu",
    constraint_values = [
        "//constraints/fpu:fpv5-d16",
    ],
    parents = [":cortex_m7"],
)
