# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# The following overlays are used to generate a generic OTP image with fake
# keys. This is useful for testing in dv_sim, fpga and verilator
# environments.
EARLGREY_OTP_SIGVERIFY_FAKE_KEYS = [
    "//sw/device/silicon_creator/rom/keys/fake/otp:json_rot_keys",
]

# This is a set of overlays to generate a generic, standard OTP image.
# Additional overlays can be applied on top to further customize the OTP.
# This set of overlays does not include any of the SECRET[0-2] partitions.
EARLGREY_STD_OTP_OVERLAYS_WITHOUT_SECRET_PARTITIONS = EARLGREY_OTP_SIGVERIFY_FAKE_KEYS + [
    "//hw/top_earlgrey/data/otp:otp_json_creator_sw_cfg",
    "//hw/top_earlgrey/data/otp:otp_json_owner_sw_cfg",
    "//hw/top_earlgrey/data/otp:otp_json_alert_digest_cfg",
    "//hw/top_earlgrey/data/otp:otp_json_hw_cfg0",
    "//hw/top_earlgrey/data/otp:otp_json_hw_cfg1",
]

# This is a set of overlays to generate a generic, standard OTP image.
# Additional overlays can be applied on top to further customize the OTP.
EARLGREY_STD_OTP_OVERLAYS = EARLGREY_STD_OTP_OVERLAYS_WITHOUT_SECRET_PARTITIONS + [
    "//hw/top_earlgrey/data/otp:otp_json_secret0",
    "//hw/top_earlgrey/data/otp:otp_json_secret1",
    "//hw/top_earlgrey/data/otp:otp_json_secret2_unlocked",
]
