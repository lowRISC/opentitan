// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#include "sw/device/silicon_creator/lib/otbn_boot_services.h"
#include "sw/device/silicon_creator/lib/attestation.h"
#include "sw/device/silicon_creator/lib/attestation_key_diversifiers.h"

#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/crypto/drivers/entropy.h"

#include "sw/device/lib/testing/flash_ctrl_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/manuf/lib/flash_info_fields.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/lib/runtime/print.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"  // Generated.


OTTF_DEFINE_TEST_CONFIG();

uint32_t certs[512];

void print_array(void *buf, size_t size, bool reverse) {
  uint8_t *b = (uint8_t *)buf;
  intptr_t inc = 1;
  if (reverse) {
    b += size - 1;
    inc = -1;
  }
  size_t count = 0;
  while (size--) {
    base_printf("%02x", *b);
    b += inc;
    count++;
    if (!reverse && count >= 40) {
      base_printf("\r\n");
      count = 0;
    }
  }
  if (count)
    base_printf("\r\n");
}

bool test_main(void) {
  LOG_INFO("Started");
  uint32_t d[11] = {0}, d0[10] = {0}, d1[10] = {0};
  // Load the boot services OTBN app.
  CHECK(otbn_boot_app_load() == kErrorOk);
  LOG_INFO("Getting private key");
  CHECK(otbn_boot_attestation_private_key(
            kTpmEkAttestationKeySeed, kOtbnBootAttestationKeyTypeTpm,
            kTpmEkKeymgrDiversifier, d0, d1) == kErrorOk);

  print_array(d0, sizeof(d0), true);
  print_array(d1, sizeof(d1), true);

  uint64_t carry = 0;
  for (size_t i = 0; i < 10; i++) {
    carry += (uint64_t)d0[i] + (uint64_t)d1[i];
    d[i] = (uint32_t)carry;
    carry >>= 32;
  }
  d[10] = (uint32_t)carry;
  LOG_INFO("Blinded D:");
  print_array(d, sizeof(d0) + 1, true);

  attestation_public_key_t public_key;
  LOG_INFO("Getting public key");
  CHECK(otbn_boot_attestation_keygen(
            kTpmEkAttestationKeySeed, kOtbnBootAttestationKeyTypeTpm,
            kTpmEkKeymgrDiversifier, &public_key) == kErrorOk);

  LOG_INFO("Public X:");
  print_array(&public_key.x, sizeof(public_key.x), true);
  LOG_INFO("Public Y:");
  print_array(&public_key.y, sizeof(public_key.y), true);

  CHECK(flash_ctrl_info_read(&kFlashCtrlInfoPageTpmCerts, 0, 512, certs) ==
        kErrorOk);
  size_t cert_size = 666;
  if ((certs[0] & 0xffff) == 0x8230) {
    cert_size = 4 + ((((certs[0]) >> 8) & 0xff00) | (certs[0] >> 24));
  }
  LOG_INFO("TPM EK cert size: %u", cert_size);
  print_array(certs, cert_size, false);
  return true;
}
