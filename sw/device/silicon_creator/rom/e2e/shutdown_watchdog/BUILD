# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules/opentitan:defs.bzl",
    "cw310_params",
    "opentitan_test",
    "rsa_key_for_lc_state",
)
load(
    "//rules:const.bzl",
    "CONST",
    "get_lc_items",
)
load(
    "//rules:opentitan.bzl",
    "RSA_ONLY_KEY_STRUCTS",
)
load(
    "//rules:otp.bzl",
    "STD_OTP_OVERLAYS",
    "otp_hex",
    "otp_image",
    "otp_json",
    "otp_partition",
)
load(
    "//rules:rom_e2e.bzl",
    "maybe_skip_in_ci",
)
load(
    "//rules:splice.bzl",
    "bitstream_splice",
)

package(default_visibility = ["//visibility:public"])

SHUTDOWN_WATCHDOG_BITE_THRESHOLDS = [
    200000,  # 1 seconds at 200 kHz
    0,  # Watchdog disabled
]

SHUTDOWN_WATCHDOG_CASES = [
    {
        "lc_state": lc_state[0],
        "lc_state_val": lc_state[1],
        # Make sure that the watchdog was not enabled so the count stayed 0.
        "exit_success": "Wait done: after [0-9]+ ms, watchdog count=0",
        "bite_threshold": bite_threshold,
    }
    for lc_state in get_lc_items(
        CONST.LCV.TEST_UNLOCKED0,
        CONST.LCV.RMA,
    )
    for bite_threshold in SHUTDOWN_WATCHDOG_BITE_THRESHOLDS
] + [
    {
        "lc_state": lc_state[0],
        "lc_state_val": lc_state[1],
        "exit_success": "Wait done: after [0-9]+ ms, watchdog count=0" if bite_threshold == 0 else "I0000[^\r\n]*\r\nROM:[0-9a-f]{8}\r\n",
        "bite_threshold": bite_threshold,
    }
    for lc_state in get_lc_items(
        CONST.LCV.DEV,
        CONST.LCV.PROD,
        CONST.LCV.PROD_END,
    )
    for bite_threshold in SHUTDOWN_WATCHDOG_BITE_THRESHOLDS
]

[
    otp_json(
        name = "otp_json_shutdown_watchdog_{}_{}".format(
            t["lc_state"],
            t["bite_threshold"],
        ),
        partitions = [
            otp_partition(
                name = "OWNER_SW_CFG",
                items = {"OWNER_SW_CFG_ROM_WATCHDOG_BITE_THRESHOLD_CYCLES": otp_hex(t["bite_threshold"])},
            ),
        ],
    )
    for t in SHUTDOWN_WATCHDOG_CASES
]

[
    otp_image(
        name = "otp_img_shutdown_watchdog_{}_{}".format(
            t["lc_state"],
            t["bite_threshold"],
        ),
        src = "//hw/ip/otp_ctrl/data:otp_json_{}".format(t["lc_state"]),
        overlays = STD_OTP_OVERLAYS + [
            ":otp_json_shutdown_watchdog_{}_{}".format(
                t["lc_state"],
                t["bite_threshold"],
            ),
        ],
    )
    for t in SHUTDOWN_WATCHDOG_CASES
]

[
    bitstream_splice(
        name = "bitstream_shutdown_watchdog_{}_{}".format(
            t["lc_state"],
            t["bite_threshold"],
        ),
        src = "//hw/bitstream/hyperdebug:rom_with_fake_keys",
        data = ":otp_img_shutdown_watchdog_{}_{}".format(
            t["lc_state"],
            t["bite_threshold"],
        ),
        meminfo = "//hw/bitstream/hyperdebug:otp_mmi",
        update_usr_access = True,
        visibility = ["//visibility:private"],
    )
    for t in SHUTDOWN_WATCHDOG_CASES
]

[
    opentitan_test(
        name = "shutdown_watchdog_{}_{}".format(
            t["lc_state"],
            t["bite_threshold"],
        ),
        srcs = ["hang_test.c"],
        cw310 = cw310_params(
            bitstream = ":bitstream_shutdown_watchdog_{}_{}".format(
                t["lc_state"],
                t["bite_threshold"],
            ),
            exit_success = t["exit_success"],
            tags = maybe_skip_in_ci(getattr(
                CONST.LCV,
                t["lc_state"].upper(),
            )),
        ),
        exec_env = {
            "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
        },
        local_defines = [
            "HANG_SECS=2",
        ],
        manifest = "//sw/device/silicon_creator/rom_ext:manifest_standard",
        rsa_key = rsa_key_for_lc_state(
            RSA_ONLY_KEY_STRUCTS,
            t["lc_state_val"],
        ),
        deps = [
            "//sw/device/lib/base:memory",
            "//sw/device/lib/dif:aon_timer",
            "//sw/device/lib/testing/test_framework:ottf_main",
        ],
    )
    for t in SHUTDOWN_WATCHDOG_CASES
]

test_suite(
    name = "rom_e2e_shutdown_watchdog",
    tags = ["manual"],
    tests = [
        "shutdown_watchdog_{}_{}".format(
            t["lc_state"],
            t["bite_threshold"],
        )
        for t in SHUTDOWN_WATCHDOG_CASES
    ],
)
