# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

DARJEELING_OTP_SIGVERIFY_FAKE_KEYS = [
]

# This is a set of overlays to generate a generic, standard OTP image.
# Additional overlays can be applied on top to further customize the OTP.
# This set of overlays does not include any of the SECRET[0-2] partitions.
DARJEELING_STD_OTP_OVERLAYS_WITHOUT_SECRET_PARTITIONS = DARJEELING_OTP_SIGVERIFY_FAKE_KEYS + [
    "@lowrisc_opentitan//hw/top_darjeeling/data/otp:otp_json_creator_sw_cfg",
    "@lowrisc_opentitan//hw/top_darjeeling/data/otp:otp_json_owner_sw_cfg",
    "@lowrisc_opentitan//hw/top_darjeeling/data/otp:otp_json_alert_digest_cfg",
    "@lowrisc_opentitan//hw/top_darjeeling/data/otp:otp_json_hw_cfg0",
    "@lowrisc_opentitan//hw/top_darjeeling/data/otp:otp_json_hw_cfg1",
]

# This is a set of overlays to generate a generic, standard OTP image.
# Additional overlays can be applied on top to further customize the OTP.
DARJEELING_STD_OTP_OVERLAYS = DARJEELING_STD_OTP_OVERLAYS_WITHOUT_SECRET_PARTITIONS + [
    "@lowrisc_opentitan//hw/top_darjeeling/data/otp:otp_json_secret0",
    "@lowrisc_opentitan//hw/top_darjeeling/data/otp:otp_json_secret1",
    "@lowrisc_opentitan//hw/top_darjeeling/data/otp:otp_json_secret2_unlocked",
]
