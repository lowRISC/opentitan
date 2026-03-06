// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/silicon_creator/manuf/base/perso_tlv_data.h"

OTTF_DEFINE_TEST_CONFIG();

enum {
  kX509Cdi1DebugOffset = 585,
  kCwtCdi1DebugOffset = 266,
};

const char kX509Cdi1DebugOff[] = {
    // kAsn1TagClassContext | DiceTcbInfoFlags (7)
    0x87,
    // 4-bit BitString
    0x02,
    0x04,
    // Debug mode = 0
    0x00,
};

const char kX509Cdi1DebugOn[] = {
    // kAsn1TagClassContext | DiceTcbInfoFlags (7)
    0x87,
    // 4-bit BitString
    0x02,
    0x04,
    // Debug mode = 1
    0x10,
};

const char kCwtCdi1DebugOff[] = {
    // map label: mode (-4670551)
    0x3a,
    0x00,
    0x47,
    0x44,
    0x56,
    // 1-byte bytestring
    0x41,
    // Debug mode = normal (1)
    0x01,
};

const char kCwtCdi1DebugOn[] = {
    // map label: mode (-4670551)
    0x3a,
    0x00,
    0x47,
    0x44,
    0x56,
    // 1-byte bytestring
    0x41,
    // Debug mode = debug (2)
    0x02,
};

static status_t test_debug_mode(void) {
  uint8_t data[2048];
  TRY(flash_ctrl_info_read(&kFlashCtrlInfoPageDiceCerts, 0,
                           sizeof(data) / sizeof(uint32_t), data));

  uint32_t offset = 0;
  size_t len = sizeof(data);
  while (true) {
    perso_tlv_cert_obj_t obj = {0};
    rom_error_t err = perso_tlv_get_cert_obj(data + offset, len, &obj);
    if (err != kErrorOk) {
      break;
    }
    offset += (obj.obj_size + 7) & ~7u;
    len -= obj.obj_size;

    LOG_INFO("%s type=%d sz=%d", obj.name, obj.obj_type, obj.obj_size);

    // Test for CDI_1
    if (memcmp(obj.name, "CDI_1", 5) != 0) {
      continue;
    }

    // Extract debug mode from the attestation
    uint8_t debug_mode = 0x42;
    if (obj.obj_type == kPersoObjectTypeX509Cert) {
      uint8_t *mode_ptr = obj.cert_body_p + kX509Cdi1DebugOffset;
      if (memcmp(mode_ptr, kX509Cdi1DebugOn, sizeof(kX509Cdi1DebugOn)) == 0) {
        debug_mode = true;
      } else if (memcmp(mode_ptr, kX509Cdi1DebugOff,
                        sizeof(kX509Cdi1DebugOff)) == 0) {
        debug_mode = false;
      } else {
        LOG_INFO("Unknown x509 debug mode");
        return INVALID_ARGUMENT();
      }
    } else if (obj.obj_type == kPersoObjectTypeCwtCert) {
      uint8_t *mode_ptr = obj.cert_body_p + kCwtCdi1DebugOffset;
      if (memcmp(mode_ptr, kCwtCdi1DebugOn, sizeof(kCwtCdi1DebugOn)) == 0) {
        debug_mode = true;
      } else if (memcmp(mode_ptr, kCwtCdi1DebugOff, sizeof(kCwtCdi1DebugOff)) ==
                 0) {
        debug_mode = false;
      } else {
        LOG_INFO("Unknown CWT debug mode");
        return INVALID_ARGUMENT();
      }
    } else {
      LOG_INFO("Unknown CDI_1 format");
      return INVALID_ARGUMENT();
    }

    // Assert the debug mode expectation
    if (debug_mode == true) {
      LOG_INFO("debug = true");
#ifdef TEST_EXPECT_DEBUG_ON
      return OK_STATUS();
#endif
    } else if (debug_mode == false) {
      LOG_INFO("debug = false");
#ifdef TEST_EXPECT_DEBUG_OFF
      return OK_STATUS();
#endif
    } else {
      LOG_INFO("Unknown debug mode");
      return INVALID_ARGUMENT();
    }
  }

  return UNKNOWN();
}

bool test_main(void) {
  status_t sts = test_debug_mode();
  if (status_err(sts)) {
    LOG_ERROR("test_debug_mode: %r", sts);
  }
  return status_ok(sts);
}
