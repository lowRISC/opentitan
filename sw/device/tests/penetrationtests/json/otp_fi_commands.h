// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_OTP_FI_COMMANDS_H_
#define OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_OTP_FI_COMMANDS_H_
#include "sw/device/lib/ujson/ujson_derive.h"
#ifdef __cplusplus
extern "C" {
#endif

#define OTPFI_MAX_OWNER_SW_CFG_SIZE 200
#define OTPFI_MAX_VENDOR_TEST_SIZE 16
#define OTPFI_MAX_HW_CFG0_SIZE 20
#define OTPFI_MAX_LC_SIZE 22

// clang-format off

#define OTPFI_SUBCOMMAND(_, value) \
    value(_, HwCfg) \
    value(_, Init) \
    value(_, LifeCycle) \
    value(_, OwnerSwCfg) \
    value(_, VendorTest)
C_ONLY(UJSON_SERDE_ENUM(OtpFiSubcommand, otp_fi_subcommand_t, OTPFI_SUBCOMMAND));
RUST_ONLY(UJSON_SERDE_ENUM(OtpFiSubcommand, otp_fi_subcommand_t, OTPFI_SUBCOMMAND, RUST_DEFAULT_DERIVE, strum::EnumString));

#define OTPFI_VENDORTEST_PARTITION(field, string) \
    field(partition_ref, uint32_t, OTPFI_MAX_VENDOR_TEST_SIZE) \
    field(partition_fi, uint32_t, OTPFI_MAX_VENDOR_TEST_SIZE) \
    field(data_faulty, bool, OTPFI_MAX_VENDOR_TEST_SIZE) \
    field(otp_status_codes, uint32_t) \
    field(otp_error_causes, uint8_t, 10) \
    field(alerts, uint32_t, 3) \
    field(ast_alerts, uint32_t, 2)
UJSON_SERDE_STRUCT(OtpFiVendortestPartition, otp_fi_vendortest_partition_t, OTPFI_VENDORTEST_PARTITION);

#define OTPFI_OWNERSWCFG_PARTITION(field, string) \
    field(partition_ref, uint32_t, OTPFI_MAX_OWNER_SW_CFG_SIZE) \
    field(partition_fi, uint32_t, OTPFI_MAX_OWNER_SW_CFG_SIZE) \
    field(data_faulty, bool, OTPFI_MAX_OWNER_SW_CFG_SIZE) \
    field(otp_status_codes, uint32_t) \
    field(otp_error_causes, uint8_t, 10) \
    field(alerts, uint32_t, 3) \
    field(ast_alerts, uint32_t, 2)
UJSON_SERDE_STRUCT(OtpFiOwnerswcfgPartition, otp_fi_ownerswcfg_partition_t, OTPFI_OWNERSWCFG_PARTITION);

#define OTPFI_HWCFG_PARTITION(field, string) \
    field(partition_ref, uint32_t, OTPFI_MAX_HW_CFG0_SIZE) \
    field(partition_fi, uint32_t, OTPFI_MAX_HW_CFG0_SIZE) \
    field(data_faulty, bool, OTPFI_MAX_HW_CFG0_SIZE) \
    field(otp_status_codes, uint32_t) \
    field(otp_error_causes, uint8_t, 10) \
    field(alerts, uint32_t, 3) \
    field(ast_alerts, uint32_t, 2)
UJSON_SERDE_STRUCT(OtpFiHwcfgPartition, otp_fi_hwcfg_partition_t, OTPFI_HWCFG_PARTITION);

#define OTPFI_LIFECYCLE_PARTITION(field, string) \
    field(partition_ref, uint32_t, OTPFI_MAX_LC_SIZE) \
    field(partition_fi, uint32_t, OTPFI_MAX_LC_SIZE) \
    field(data_faulty, bool, OTPFI_MAX_LC_SIZE) \
    field(otp_status_codes, uint32_t) \
    field(otp_error_causes, uint8_t, 10) \
    field(alerts, uint32_t, 3) \
    field(ast_alerts, uint32_t, 2)
UJSON_SERDE_STRUCT(OtpFiLifecyclePartition, otp_fi_lifecycle_partition_t, OTPFI_LIFECYCLE_PARTITION);

// clang-format on

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_OTP_FI_COMMANDS_H_
