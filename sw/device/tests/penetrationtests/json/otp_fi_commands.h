// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_OTP_FI_COMMANDS_H_
#define OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_OTP_FI_COMMANDS_H_
#include "sw/device/lib/ujson/ujson_derive.h"
#ifdef __cplusplus
extern "C" {
#endif

// clang-format off

#define OTPFI_SUBCOMMAND(_, value) \
    value(_, HwCfg) \
    value(_, Init) \
    value(_, LifeCycle) \
    value(_, OwnerSwCfg) \
    value(_, VendorTest)
UJSON_SERDE_ENUM(OtpFiSubcommand, otp_fi_subcommand_t, OTPFI_SUBCOMMAND);

#define OTPFI_VENDORTEST_PARTITION(field, string) \
    field(vendor_test_comp, uint32_t, 16) \
    field(vendor_test_fi, uint32_t, 16) \
    field(otp_status_codes, uint32_t) \
    field(otp_error_causes, uint8_t, 10) \
    field(alerts, uint32_t, 3)
UJSON_SERDE_STRUCT(OtpFiVendortestPartition, otp_fi_vendortest_partition_t, OTPFI_VENDORTEST_PARTITION);

#define OTPFI_OWNERSWCFG_PARTITION(field, string) \
    field(owner_sw_cfg_comp, uint32_t, 200) \
    field(owner_sw_cfg_fi, uint32_t, 200) \
    field(otp_status_codes, uint32_t) \
    field(otp_error_causes, uint8_t, 10) \
    field(alerts, uint32_t, 3)
UJSON_SERDE_STRUCT(OtpFiOwnerswcfgPartition, otp_fi_ownerswcfg_partition_t, OTPFI_OWNERSWCFG_PARTITION);

#define OTPFI_HWCFG_PARTITION(field, string) \
    field(hw_cfg_comp, uint32_t, 20) \
    field(hw_cfg_fi, uint32_t, 20) \
    field(otp_status_codes, uint32_t) \
    field(otp_error_causes, uint8_t, 10) \
    field(alerts, uint32_t, 3)
UJSON_SERDE_STRUCT(OtpFiHwcfgPartition, otp_fi_hwcfg_partition_t, OTPFI_HWCFG_PARTITION);

#define OTPFI_LIFECYCLE_PARTITION(field, string) \
    field(life_cycle_comp, uint32_t, 22) \
    field(life_cycle_fi, uint32_t, 22) \
    field(otp_status_codes, uint32_t) \
    field(otp_error_causes, uint8_t, 10) \
    field(alerts, uint32_t, 3)
UJSON_SERDE_STRUCT(OtpFiLifecyclePartition, otp_fi_lifecycle_partition_t, OTPFI_LIFECYCLE_PARTITION);

// clang-format on

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_OTP_FI_COMMANDS_H_
