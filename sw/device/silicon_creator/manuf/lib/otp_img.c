// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#include "sw/device/silicon_creator/manuf/lib/otp_img.h"

#include "sw/device/lib/testing/otp_ctrl_testutils.h"
#include "sw/device/silicon_creator/manuf/lib/otp_img_types.h"
#include "sw/ip/otp_ctrl/dif/dif_otp_ctrl.h"
#include "sw/lib/sw/device/base/status.h"

status_t otp_img_write(const dif_otp_ctrl_t *otp,
                       dif_otp_ctrl_partition_t partition, const otp_kv_t *kv,
                       size_t len) {
  for (size_t i = 0; i < len; ++i) {
    uint32_t offset;
    TRY(dif_otp_ctrl_relative_address(partition, kv[i].offset, &offset));
    switch (kv[i].type) {
      case kOptValTypeUint32Buff:
        TRY(otp_ctrl_testutils_dai_write32(otp, partition, offset,
                                           kv[i].value32, kv[i].num_values));
        break;
      case kOptValTypeUint64Buff:
        TRY(otp_ctrl_testutils_dai_write64(otp, partition, offset,
                                           kv[i].value64, kv[i].num_values));
        break;
      case kOptValTypeUint64Rnd:
        return UNIMPLEMENTED();
      default:
        return INTERNAL();
    }
  }
  return OK_STATUS();
}
