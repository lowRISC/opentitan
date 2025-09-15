# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#

load("//rules/opentitan:hw.bzl", "opentitan_top")
load("//hw/top_verbano/data/autogen:defs.bzl", "EARLGREY_IPS")
load("//hw/top_verbano/data/otp:defs.bzl", "EARLGREY_OTP_SIGVERIFY_FAKE_KEYS", "EARLGREY_STD_OTP_OVERLAYS")

EARLGREY = opentitan_top(
    name = "verbano",
    hjson = "//hw/top_verbano/data/autogen:top_verbano.gen.hjson",
    top_lib = "//hw/top_verbano/sw/autogen:top_verbano",
    top_ld = "//hw/top_verbano/sw/autogen:top_verbano_memory",
    otp_map = "//hw/top_verbano/data/otp:otp_ctrl_mmap.hjson",
    std_otp_overlay = EARLGREY_STD_OTP_OVERLAYS,
    otp_sigverify_fake_keys = EARLGREY_OTP_SIGVERIFY_FAKE_KEYS,
    ips = EARLGREY_IPS,
    secret_cfgs = {
        "testing": "//hw/top_verbano/data/autogen:top_verbano.secrets.testing.gen.hjson",
    },
)
