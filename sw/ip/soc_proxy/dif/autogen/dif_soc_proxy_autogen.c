// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// THIS FILE HAS BEEN GENERATED, DO NOT EDIT MANUALLY. COMMAND:
// util/make_new_dif.py --mode=regen --only=autogen

#include "sw/ip/soc_proxy/dif/autogen/dif_soc_proxy_autogen.h"

#include <stdint.h>

#include "sw/ip/base/dif/dif_base.h"

#include "soc_proxy_regs.h"  // Generated.

OT_WARN_UNUSED_RESULT
dif_result_t dif_soc_proxy_init(mmio_region_t base_addr,
                                dif_soc_proxy_t *soc_proxy) {
  if (soc_proxy == NULL) {
    return kDifBadArg;
  }

  soc_proxy->base_addr = base_addr;

  return kDifOk;
}

dif_result_t dif_soc_proxy_alert_force(const dif_soc_proxy_t *soc_proxy,
                                       dif_soc_proxy_alert_t alert) {
  if (soc_proxy == NULL) {
    return kDifBadArg;
  }

  bitfield_bit32_index_t alert_idx;
  switch (alert) {
    case kDifSocProxyAlertFatalAlertIntg:
      alert_idx = SOC_PROXY_ALERT_TEST_FATAL_ALERT_INTG_BIT;
      break;
    default:
      return kDifBadArg;
  }

  uint32_t alert_test_reg = bitfield_bit32_write(0, alert_idx, true);
  mmio_region_write32(soc_proxy->base_addr,
                      (ptrdiff_t)SOC_PROXY_ALERT_TEST_REG_OFFSET,
                      alert_test_reg);

  return kDifOk;
}
