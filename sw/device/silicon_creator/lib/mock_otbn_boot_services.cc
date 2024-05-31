// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/mock_otbn_boot_services.h"

#include "sw/device/silicon_creator/lib/otbn_boot_services.h"

namespace rom_test {
extern "C" {

rom_error_t otbn_boot_app_load() {
  return MockOtbnBootServices::Instance().otbn_boot_app_load();
}

rom_error_t otbn_boot_attestation_keygen(
    attestation_key_seed_t additional_seed,
    otbn_boot_attestation_key_type_t key_type,
    sc_keymgr_diversification_t diversification,
    attestation_public_key_t *public_key) {
  return MockOtbnBootServices::Instance().otbn_boot_attestation_keygen(
      additional_seed, key_type, diversification, public_key);
}

rom_error_t otbn_boot_attestation_key_save(
    attestation_key_seed_t additional_seed,
    otbn_boot_attestation_key_type_t key_type,
    sc_keymgr_diversification_t diversification) {
  return MockOtbnBootServices::Instance().otbn_boot_attestation_key_save(
      additional_seed, key_type, diversification);
}

rom_error_t otbn_boot_attestation_key_clear() {
  return MockOtbnBootServices::Instance().otbn_boot_attestation_key_clear();
}

rom_error_t otbn_boot_attestation_endorse(const hmac_digest_t *digest,
                                          attestation_signature_t *sig) {
  return MockOtbnBootServices::Instance().otbn_boot_attestation_endorse(digest,
                                                                        sig);
}

rom_error_t otbn_boot_sigverify(const attestation_public_key_t *key,
                                const attestation_signature_t *sig,
                                const hmac_digest_t *digest,
                                uint32_t *recovered_r) {
  return MockOtbnBootServices::Instance().otbn_boot_sigverify(key, sig, digest,
                                                              recovered_r);
}

}  // extern "C"
}  // namespace rom_test
