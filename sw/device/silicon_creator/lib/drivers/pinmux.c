// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/pinmux.h"

#include "hw/top/dt/dt_api.h"
#include "hw/top/dt/dt_pinmux.h"
#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/csr.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/base/chip.h"

#include "hw/top/pinmux_regs.h"

static inline uint32_t pinmux_base(void) {
  return dt_pinmux_primary_reg_block(kDtPinmuxAon);
}

#define REGWEN_CHECK(regwen, register)                          \
  (((regwen) & (1 << PINMUX_##register##_REGWEN_0_EN_0_BIT)) != \
   PINMUX_##register##_REGWEN_0_REG_RESVAL);

OT_WARN_UNUSED_RESULT
static rom_error_t pad_reg_addr(dt_pad_t pad, uintptr_t base_mio_reg_addr,
                                uintptr_t base_dio_reg_addr,
                                uintptr_t *reg_addr) {
  dt_pad_type_t pad_type = dt_pad_type(pad);
  if (pad_type == kDtPadTypeUnspecified) {
    return kErrorPinMuxInvalidPad;
  }

  switch (pad_type) {
    case kDtPadTypeMio:
      *reg_addr = pinmux_base() + base_mio_reg_addr +
                  (dt_pad_mio_pad_index(pad) * sizeof(uint32_t));
      break;
    case kDtPadTypeDio:
      *reg_addr = pinmux_base() + base_dio_reg_addr +
                  (dt_pad_dio_pad_index(pad) * sizeof(uint32_t));
      break;
    default:
      return kErrorPinMuxInvalidPad;
  }

  return kErrorOk;
}

OT_WARN_UNUSED_RESULT
static rom_error_t pad_attr_reg_addr(dt_pad_t pad, uintptr_t *reg_addr) {
  return pad_reg_addr(pad, PINMUX_MIO_PAD_ATTR_0_REG_OFFSET,
                      PINMUX_DIO_PAD_ATTR_0_REG_OFFSET, reg_addr);
}

OT_WARN_UNUSED_RESULT
static rom_error_t pad_attr_regwen_reg_addr(dt_pad_t pad, uintptr_t *reg_addr) {
  return pad_reg_addr(pad, PINMUX_MIO_PAD_ATTR_REGWEN_0_REG_OFFSET,
                      PINMUX_DIO_PAD_ATTR_REGWEN_0_REG_OFFSET, reg_addr);
}

OT_WARN_UNUSED_RESULT
static bool pad_attr_is_locked(dt_pad_t pad) {
  uintptr_t reg_addr;

  HARDENED_RETURN_IF_ERROR(pad_attr_regwen_reg_addr(pad, &reg_addr));

  uint32_t regwen = abs_mmio_read32(reg_addr);

  return REGWEN_CHECK(regwen, DIO_PAD_ATTR);
}

OT_WARN_UNUSED_RESULT
static bool pad_outsel_is_locked(dt_pad_t pad) {
  dt_pinmux_mio_out_t mio_pad_output = dt_pad_mio_out(pad);
  uintptr_t reg_addr = pinmux_base() + PINMUX_MIO_OUTSEL_REGWEN_0_REG_OFFSET +
                       (mio_pad_output * sizeof(uint32_t));
  uint32_t regwen = abs_mmio_read32(reg_addr);

  return REGWEN_CHECK(regwen, MIO_OUTSEL);
}

OT_WARN_UNUSED_RESULT
static bool periph_insel_is_locked(dt_periph_io_t periph_io) {
  dt_pinmux_peripheral_in_t periph_input =
      dt_periph_io_mio_periph_input(periph_io);

  uintptr_t reg_addr = pinmux_base() +
                       PINMUX_MIO_PERIPH_INSEL_REGWEN_0_REG_OFFSET +
                       (periph_input * sizeof(uint32_t));
  uint32_t regwen = abs_mmio_read32(reg_addr);

  return REGWEN_CHECK(regwen, MIO_PERIPH_INSEL);
}

/**
 * Delay while we wait for pinmux values to stabilize after changing resistor
 * pull-up/down values.
 */
static void pinmux_prop_delay(void) {
  // Wait for pull downs to propagate to the physical pads.
  CSR_WRITE(CSR_REG_MCYCLE, 0);
  uint32_t mcycle;
  do {
    CSR_READ(CSR_REG_MCYCLE, &mcycle);
  } while (mcycle < PINMUX_PAD_ATTR_PROP_CYCLES);
}

OT_WARN_UNUSED_RESULT
static rom_error_t pinmux_configure_pull(dt_pad_t pad, bool enable, bool up) {
  if (pad_attr_is_locked(pad)) {
    return kErrorPinMuxLockedPad;
  }

  uintptr_t reg_addr;
  uint32_t reg_value = 0;

  reg_value = bitfield_bit32_write(reg_value,
                                   PINMUX_MIO_PAD_ATTR_0_PULL_EN_0_BIT, enable);
  reg_value = bitfield_bit32_write(reg_value,
                                   PINMUX_MIO_PAD_ATTR_0_PULL_SELECT_0_BIT, up);

  HARDENED_RETURN_IF_ERROR(pad_attr_reg_addr(pad, &reg_addr));

  abs_mmio_write32(reg_addr, reg_value);

  pinmux_prop_delay();

  return kErrorOk;
}

OT_WARN_UNUSED_RESULT
static rom_error_t periph_select_input(dt_periph_io_t periph_io, dt_pad_t pad) {
  dt_pinmux_peripheral_in_t periph_input =
      dt_periph_io_mio_periph_input(periph_io);
  dt_pinmux_insel_t mio_pad_insel = dt_pad_mio_insel(pad);

  if (periph_input >= PINMUX_PARAM_N_MIO_PERIPH_IN) {
    return kErrorPinMuxInvalidPeriphIo;
  }

  if (mio_pad_insel == 0) {
    return kErrorPinMuxInvalidPad;
  }

  if (periph_insel_is_locked(periph_io)) {
    return kErrorPinMuxLockedPeriphIo;
  }

  uintptr_t reg_addr = pinmux_base() + PINMUX_MIO_PERIPH_INSEL_0_REG_OFFSET +
                       (periph_input * sizeof(uint32_t));
  uint32_t reg_value = bitfield_field32_write(
      0, PINMUX_MIO_PERIPH_INSEL_0_IN_0_FIELD, mio_pad_insel);

  abs_mmio_write32(reg_addr, reg_value);

  return kErrorOk;
}

OT_WARN_UNUSED_RESULT
static rom_error_t pad_select_output(dt_periph_io_t periph_io, dt_pad_t pad) {
  dt_pinmux_outsel_t periph_output = dt_periph_io_mio_outsel(periph_io);
  dt_pinmux_mio_out_t mio_pad_output = dt_pad_mio_out(pad);

  if (periph_output >= (3 + PINMUX_PARAM_N_MIO_PERIPH_OUT)) {
    return kErrorPinMuxInvalidPeriphIo;
  }

  if (pad_outsel_is_locked(pad)) {
    return kErrorPinMuxLockedPad;
  }

  uintptr_t reg_addr = pinmux_base() + PINMUX_MIO_OUTSEL_0_REG_OFFSET +
                       (mio_pad_output * sizeof(uint32_t));
  uint32_t reg_value =
      bitfield_field32_write(0, PINMUX_MIO_OUTSEL_0_OUT_0_FIELD, periph_output);

  abs_mmio_write32(reg_addr, reg_value);

  return kErrorOk;
}

OT_WARN_UNUSED_RESULT
rom_error_t pinmux_enable_pull_up(dt_pad_t pad) {
  return pinmux_configure_pull(pad, true, true);
}

OT_WARN_UNUSED_RESULT
rom_error_t pinmux_enable_pull_down(dt_pad_t pad) {
  return pinmux_configure_pull(pad, true, false);
}

OT_WARN_UNUSED_RESULT
rom_error_t pinmux_disable_pull(dt_pad_t pad) {
  return pinmux_configure_pull(pad, false, false);
}

OT_WARN_UNUSED_RESULT
rom_error_t pinmux_connect(dt_periph_io_t periph_io, dt_pad_t pad,
                           dt_periph_io_dir_t dir) {
  switch (dt_periph_io_type(periph_io)) {
    case kDtPeriphIoTypeMio:
      if (dt_pad_type(pad) != kDtPadTypeMio) {
        return kErrorPinMuxInvalidPad;
      }

      // Input configuration
      if (dir == kDtPeriphIoDirIn || dir == kDtPeriphIoDirInout) {
        HARDENED_RETURN_IF_ERROR(periph_select_input(periph_io, pad));
      }

      // Output configuration
      if (dir == kDtPeriphIoDirOut || dir == kDtPeriphIoDirInout) {
        HARDENED_RETURN_IF_ERROR(pad_select_output(periph_io, pad));
      } else if (dt_periph_io_dir(periph_io) == kDtPeriphIoDirInout) {
        // Set output to high-Z for input only peripherals.
        HARDENED_RETURN_IF_ERROR(
            pad_select_output(kDtPeriphIoConstantHighZ, pad));
      }
      return kErrorOk;
    case kDtPeriphIoTypeDio:
      // Nothing to do but to check that the pad and the peripheral IO are
      // connected.
      if (dt_pad_type(pad) != kDtPadTypeDio) {
        return kErrorPinMuxInvalidPad;
      }

      if (dt_periph_io_dio_pad(periph_io) != pad) {
        return kErrorPinMuxInvalidPeriphIo;
      }

      // Make sure that the directions are compatible.
      dt_periph_io_dir_t io_dir = dt_periph_io_dir(periph_io);
      if ((io_dir == kDtPeriphIoDirIn || io_dir == kDtPeriphIoDirOut) &&
          dir != io_dir) {
        return kErrorPinMuxInvalidPeriphIo;
      }
      return kErrorOk;
    default:
      return kErrorPinMuxInvalidPeriphIo;
  }
}
