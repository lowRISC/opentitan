// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_pinmux.h"

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/mmio.h"
#include "pinmux_regs.h"  // Generated.

// If either of these static assertions fail, then the assumptions in this DIF
// implementation should be revisited. In particular, `plic_target_reg_offsets`
// may need updating,
_Static_assert(PINMUX_PERIPH_INSEL_IN_FIELD_WIDTH == 6,
               "Pinmux instantiation parameters have changed.");
_Static_assert(PINMUX_PERIPH_INSEL_IN_FIELDS_PER_REG == 5,
               "Pinmux instantiation parameters have changed.");
_Static_assert(PINMUX_PERIPH_INSEL_MULTIREG_COUNT == 7,
               "Pinmux instantiation parameters have changed.");

_Static_assert(PINMUX_MIO_OUTSEL_OUT_FIELD_WIDTH == 6,
               "Pinmux instantiation parameters have changed.");
_Static_assert(PINMUX_MIO_OUTSEL_OUT_FIELDS_PER_REG == 5,
               "Pinmux instantiation parameters have changed.");
_Static_assert(PINMUX_MIO_OUTSEL_MULTIREG_COUNT == 7,
               "Pinmux instantiation parameters have changed.");

#define PINMUX_INSEL_RESET_DEFAULT 0
#define PINMUX_OUTSEL_RESET_DEFAULT 0x2082082

const uint32_t kDifPinmuxPeripheralInLast = PINMUX_PARAM_NMIOPERIPHIN - 1;
const uint32_t kDifPinmuxMioOutLast = PINMUX_PARAM_NMIOPADS - 1;

#define PINMUX_INSEL_FIRST_IN 2
const uint32_t kDifPinmuxInselFirstIn = PINMUX_INSEL_FIRST_IN;
const uint32_t kDifPinmuxInselLast =
    PINMUX_INSEL_FIRST_IN + (PINMUX_PARAM_NMIOPADS - 1);

#define PINMUX_OUTSEL_FIRST_OUT 3
const uint32_t kDifPinmuxOutselFirstOut = PINMUX_OUTSEL_FIRST_OUT;
const uint32_t kDifPinmuxOutselLast =
    PINMUX_OUTSEL_FIRST_OUT + (PINMUX_PARAM_NMIOPERIPHOUT - 1);

/**
 * Insel/outsel register offset based on a given Padring MIO/Peripheral ID.
 */
static ptrdiff_t multireg_offset(ptrdiff_t base, uint32_t id,
                                 uint32_t fields_per_reg) {
  size_t register_index = id / fields_per_reg;
  ptrdiff_t register_offset = base + (register_index * sizeof(uint32_t));

  return register_offset;
}

/**
 * Field offset inside an insel/outsel register based on a given Padring
 * MIO/Peripheral ID.
 */
static size_t multireg_field_offset(uint32_t id, uint32_t fields_per_reg,
                                    uint32_t field_width) {
  size_t field_index = id % fields_per_reg;
  return field_index * field_width;
}

static void dif_pinmux_reset(const dif_pinmux_t *pinmux) {
  // Reset all of the insel registers (multireg) to the reset value.
  for (int i = 0; i < PINMUX_PERIPH_INSEL_MULTIREG_COUNT; ++i) {
    ptrdiff_t register_offset =
        PINMUX_PERIPH_INSEL0_REG_OFFSET + (i * sizeof(uint32_t));
    mmio_region_write32(pinmux->base_addr, register_offset,
                        PINMUX_INSEL_RESET_DEFAULT);
  }

  // Reset all of the outsel registers (multireg) to the reset value.
  for (int i = 0; i < PINMUX_MIO_OUTSEL_MULTIREG_COUNT; ++i) {
    ptrdiff_t register_offset =
        PINMUX_MIO_OUTSEL0_REG_OFFSET + (i * sizeof(uint32_t));
    mmio_region_write32(pinmux->base_addr, register_offset,
                        PINMUX_OUTSEL_RESET_DEFAULT);
  }
}

dif_pinmux_init_result_t dif_pinmux_init(mmio_region_t base_addr,
                                         dif_pinmux_t *pinmux) {
  if (pinmux == NULL) {
    return kDifPinmuxInitBadArg;
  }

  // Check if pinmux registers are locked.
  bool write_enabled = mmio_region_get_bit32(base_addr, PINMUX_REGEN_REG_OFFSET,
                                             PINMUX_REGEN_WEN);
  if (!write_enabled) {
    return kDifPinmuxInitLocked;
  }

  pinmux->base_addr = base_addr;

  dif_pinmux_reset(pinmux);

  return kDifPinmuxInitOk;
}

dif_pinmux_result_t dif_pinmux_registers_lock(dif_pinmux_t *pinmux) {
  if (pinmux == NULL) {
    return kDifPinmuxBadArg;
  }

  mmio_region_write32(pinmux->base_addr, PINMUX_REGEN_REG_OFFSET, 0);

  return kDifPinmuxOk;
}

dif_pinmux_result_t dif_pinmux_insel_set(
    const dif_pinmux_t *pinmux, dif_pinmux_peripheral_in_t peripheral_in,
    dif_pinmux_insel_t mio_in_select) {
  if (pinmux == NULL || peripheral_in > kDifPinmuxPeripheralInLast ||
      mio_in_select > kDifPinmuxInselLast) {
    return kDifPinmuxBadArg;
  }

  size_t field_offset = multireg_field_offset(
      peripheral_in, PINMUX_PERIPH_INSEL_IN_FIELDS_PER_REG,
      PINMUX_PERIPH_INSEL_IN_FIELD_WIDTH);

  bitfield_field32_t field = {
      .mask = PINMUX_PERIPH_INSEL0_IN0_MASK,
      .index = field_offset,
      .value = mio_in_select,
  };

  ptrdiff_t register_offset =
      multireg_offset(PINMUX_PERIPH_INSEL0_REG_OFFSET, peripheral_in,
                      PINMUX_PERIPH_INSEL_IN_FIELDS_PER_REG);

  mmio_region_nonatomic_set_field32(pinmux->base_addr, register_offset, field);

  return kDifPinmuxOk;
}

dif_pinmux_result_t dif_pinmux_outsel_set(
    const dif_pinmux_t *pinmux, dif_pinmux_mio_out_t mio_out,
    dif_pinmux_outsel_t peripheral_out_select) {
  if (pinmux == NULL || mio_out > kDifPinmuxMioOutLast ||
      peripheral_out_select > kDifPinmuxOutselLast) {
    return kDifPinmuxBadArg;
  }

  size_t field_offset =
      multireg_field_offset(mio_out, PINMUX_MIO_OUTSEL_OUT_FIELDS_PER_REG,
                            PINMUX_MIO_OUTSEL_OUT_FIELD_WIDTH);

  bitfield_field32_t field = {
      .mask = PINMUX_MIO_OUTSEL0_OUT0_MASK,
      .index = field_offset,
      .value = peripheral_out_select,
  };

  ptrdiff_t register_offset =
      multireg_offset(PINMUX_MIO_OUTSEL0_REG_OFFSET, mio_out,
                      PINMUX_MIO_OUTSEL_OUT_FIELDS_PER_REG);

  mmio_region_nonatomic_set_field32(pinmux->base_addr, register_offset, field);

  return kDifPinmuxOk;
}
