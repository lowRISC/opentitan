platform(
    name = "cortex_m",
    constraint_values = [
        "@platforms//os:none",
        "//constraints/fpu:none",
        "@platforms//cpu:armv6-m",
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
        "@platforms//cpu:armv7-m",
    ],
    parents = [":cortex_m"],
)

platform(
    name = "cortex_m4",
    constraint_values = [
        "@platforms//cpu:armv7-m",
    ],
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
        "@platforms//cpu:armv7e-m",
    ],
    parents = [":cortex_m"],
)

platform(
    name = "cortex_m7_fpu",
    constraint_values = [
        "@platforms//cpu:armv7e-m",
        "//constraints/fpu:fpv5-d16",
    ],
    parents = [":cortex_m"],
)
