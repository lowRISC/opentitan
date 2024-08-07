// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/json/provisioning_data.h"
#include "sw/device/lib/testing/test_framework/status.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/silicon_creator/lib/cert/cert.h"

status_t personalize_extension_pre_cert_endorse(
    ujson_t *uj, manuf_certgen_inputs_t *certgen_inputs,
    manuf_certs_t *tbs_certs, cert_flash_info_layout_t *cert_flash_layout) {
  LOG_INFO("Running example pre-cert-endorsement perso extension ...");
  return OK_STATUS();
}

status_t personalize_extension_post_cert_endorse(
    ujson_t *uj, manuf_certs_t *endorsed_certs,
    cert_flash_info_layout_t *cert_flash_layout) {
  LOG_INFO("Running example post-cert-endorsement perso extension ...");
  return OK_STATUS();
}
