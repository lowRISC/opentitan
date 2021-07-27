// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/pinmux.h"

#include "sw/device/lib/base/memory.h"
#include "sw/device/silicon_creator/lib/base/abs_mmio.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "pinmux_regs.h"  // Generated.

/**
 * Pad attribute fields.
 *
 * TODO: it would be better if these were generated.
 */
#define PAD_ATTR_PULL_DISABLE (0 << 2)
#define PAD_ATTR_PULL_ENABLE (1 << 2)
#define PAD_ATTR_PULL_DOWN (0 << 3)
#define PAD_ATTR_PULL_UP (1 << 3)

/**
 * Pad attribute values.
 *
 * Only specifies pad attribute combinations used by this driver and the default
 * for documentation purposes.
 */
typedef enum pad_attr {
  kPadAttrDefault = PAD_ATTR_PULL_DISABLE,
  kPadAttrPullDown = PAD_ATTR_PULL_ENABLE | PAD_ATTR_PULL_DOWN,
} pad_attr_t;

/**
 * Individual MIO pad to pad attribute mapping.
 */
typedef struct pad_config {
  top_earlgrey_pinmux_mio_out_t pad;
  pad_attr_t attr;
} pad_config_t;

/**
 * MIO pad to pad attribute mappings.
 */
static const pad_config_t kPadConfigs[] = {
    /**
     * Software straps are configured as pull down so that only a strong pull up
     * on the input reads as 1.
     */
    {.pad = kTopEarlgreyPinmuxMioOutIoc0, .attr = kPadAttrPullDown},
    {.pad = kTopEarlgreyPinmuxMioOutIoc1, .attr = kPadAttrPullDown},
    {.pad = kTopEarlgreyPinmuxMioOutIoc2, .attr = kPadAttrPullDown},
};

/**
 * A peripheral input and MIO pad to link it to.
 */
typedef struct pinmux_input {
  top_earlgrey_pinmux_peripheral_in_t periph;
  top_earlgrey_pinmux_insel_t pad;
} pinmux_input_t;

/**
 * Peripheral input to MIO pad mappings.
 */
static const pinmux_input_t kPinmuxInputs[] = {
    /**
     * Software strap pins are connected to the GPIO module.
     */
    {.periph = kTopEarlgreyPinmuxPeripheralInGpioGpio0,
     .pad = kTopEarlgreyPinmuxInselIoc0},
    {.periph = kTopEarlgreyPinmuxPeripheralInGpioGpio1,
     .pad = kTopEarlgreyPinmuxInselIoc1},
    {.periph = kTopEarlgreyPinmuxPeripheralInGpioGpio2,
     .pad = kTopEarlgreyPinmuxInselIoc2},
};

/**
 * An MIO pad and a peripheral output to link it to.
 */
typedef struct pinmux_output {
  top_earlgrey_pinmux_mio_out_t pad;
  top_earlgrey_pinmux_outsel_t periph;
} pinmux_output_t;

/**
 * MIO pad to peripheral output mappings.
 */
static const pinmux_output_t kPinmuxOutputs[] = {
    /**
     * UART
     */
    {.pad = kTopEarlgreyPinmuxMioOutIoc11,
     .periph = kTopEarlgreyPinmuxOutselUart0Tx},
};

void pinmux_init(void) {
  // Configure pad attributes.
  const uint32_t kConfigBase =
      TOP_EARLGREY_PINMUX_AON_BASE_ADDR + PINMUX_MIO_PAD_ATTR_0_REG_OFFSET;
  for (uint32_t i = 0; i < ARRAYSIZE(kPadConfigs); ++i) {
    uint32_t reg = kPadConfigs[i].pad * sizeof(uint32_t);
    uint32_t val = kPadConfigs[i].attr;
    abs_mmio_write32(kConfigBase + reg, val);
  }

  // Set the input pad for each specified peripheral input.
  const uint32_t kInputBase =
      TOP_EARLGREY_PINMUX_AON_BASE_ADDR + PINMUX_MIO_PERIPH_INSEL_0_REG_OFFSET;
  for (uint32_t i = 0; i < ARRAYSIZE(kPinmuxInputs); ++i) {
    uint32_t reg = kPinmuxInputs[i].periph * sizeof(uint32_t);
    uint32_t val = kPinmuxInputs[i].pad;
    abs_mmio_write32(kInputBase + reg, val);
  }

  // Set the peripheral output for each specified output pad.
  const uint32_t kOutputBase =
      TOP_EARLGREY_PINMUX_AON_BASE_ADDR + PINMUX_MIO_OUTSEL_0_REG_OFFSET;
  for (uint32_t i = 0; i < ARRAYSIZE(kPinmuxOutputs); ++i) {
    uint32_t reg = kPinmuxOutputs[i].pad * sizeof(uint32_t);
    uint32_t val = kPinmuxOutputs[i].periph;
    abs_mmio_write32(kOutputBase + reg, val);
  }
}
