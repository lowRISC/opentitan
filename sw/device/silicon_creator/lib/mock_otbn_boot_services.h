// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_MOCK_OTBN_BOOT_SERVICES_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_MOCK_OTBN_BOOT_SERVICES_H_

#include "sw/device/lib/base/global_mock.h"
#include "sw/device/silicon_creator/lib/otbn_boot_services.h"
#include "sw/device/silicon_creator/testing/rom_test.h"

namespace rom_test {
namespace internal {

/**
 * Mock class for otbn_boot_services.h.
 */
class MockOtbnBootServices
    : public global_mock::GlobalMock<MockOtbnBootServices> {
 public:
  MOCK_METHOD(rom_error_t, otbn_boot_app_load, ());
  MOCK_METHOD(rom_error_t, otbn_boot_attestation_keygen,
              (attestation_key_seed_t, otbn_boot_attestation_key_type_t,
               sc_keymgr_diversification_t, attestation_public_key_t *));
  MOCK_METHOD(rom_error_t, otbn_boot_attestation_key_save,
              (attestation_key_seed_t, otbn_boot_attestation_key_type_t,
               sc_keymgr_diversification_t));
  MOCK_METHOD(rom_error_t, otbn_boot_attestation_key_clear, ());
  MOCK_METHOD(rom_error_t, otbn_boot_attestation_endorse,
              (const hmac_digest_t *, attestation_signature_t *));
  MOCK_METHOD(rom_error_t, otbn_boot_sigverify,
              (const attestation_public_key_t *,
               const attestation_signature_t *, const hmac_digest_t *,
               uint32_t *));
};

}  // namespace internal

using MockOtbnBootServices =
    testing::StrictMock<internal::MockOtbnBootServices>;
using NiceMockOtbnBootServices =
    testing::NiceMock<internal::MockOtbnBootServices>;

}  // namespace rom_test

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_MOCK_OTBN_BOOT_SERVICES_H_
