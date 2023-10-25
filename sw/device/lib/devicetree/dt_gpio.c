// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/devicetree/dt_gpio.h"

#include <zephyr/devicetree.h>

#define DT_DRV_COMPAT lowrisc_gpio

typedef struct dt_device_gpio {
  int32_t id;
  uintptr_t reg_addr;
  int32_t irq[kDtGpioIrqTypeCount];
} dt_device_gpio_t;

static const dt_device_gpio_t dev[] = {
#define DT_DEVICE_ENTRY(inst)                                              \
  [inst] = {                                                               \
      .id = DT_INST_DEP_ORD(inst),                                         \
      .reg_addr = DT_INST_REG_ADDR(inst),                                  \
      .irq =                                                               \
          {                                                                \
              [kDtGpioIrqGpio0] = DT_INST_IRQ_BY_NAME(inst, gpio0, irq),   \
              [kDtGpioIrqGpio1] = DT_INST_IRQ_BY_NAME(inst, gpio1, irq),   \
              [kDtGpioIrqGpio2] = DT_INST_IRQ_BY_NAME(inst, gpio2, irq),   \
              [kDtGpioIrqGpio3] = DT_INST_IRQ_BY_NAME(inst, gpio3, irq),   \
              [kDtGpioIrqGpio4] = DT_INST_IRQ_BY_NAME(inst, gpio4, irq),   \
              [kDtGpioIrqGpio5] = DT_INST_IRQ_BY_NAME(inst, gpio5, irq),   \
              [kDtGpioIrqGpio6] = DT_INST_IRQ_BY_NAME(inst, gpio6, irq),   \
              [kDtGpioIrqGpio7] = DT_INST_IRQ_BY_NAME(inst, gpio7, irq),   \
              [kDtGpioIrqGpio8] = DT_INST_IRQ_BY_NAME(inst, gpio8, irq),   \
              [kDtGpioIrqGpio9] = DT_INST_IRQ_BY_NAME(inst, gpio9, irq),   \
              [kDtGpioIrqGpio10] = DT_INST_IRQ_BY_NAME(inst, gpio10, irq), \
              [kDtGpioIrqGpio11] = DT_INST_IRQ_BY_NAME(inst, gpio11, irq), \
              [kDtGpioIrqGpio12] = DT_INST_IRQ_BY_NAME(inst, gpio12, irq), \
              [kDtGpioIrqGpio13] = DT_INST_IRQ_BY_NAME(inst, gpio13, irq), \
              [kDtGpioIrqGpio14] = DT_INST_IRQ_BY_NAME(inst, gpio14, irq), \
              [kDtGpioIrqGpio15] = DT_INST_IRQ_BY_NAME(inst, gpio15, irq), \
              [kDtGpioIrqGpio16] = DT_INST_IRQ_BY_NAME(inst, gpio16, irq), \
              [kDtGpioIrqGpio17] = DT_INST_IRQ_BY_NAME(inst, gpio17, irq), \
              [kDtGpioIrqGpio18] = DT_INST_IRQ_BY_NAME(inst, gpio18, irq), \
              [kDtGpioIrqGpio19] = DT_INST_IRQ_BY_NAME(inst, gpio19, irq), \
              [kDtGpioIrqGpio20] = DT_INST_IRQ_BY_NAME(inst, gpio20, irq), \
              [kDtGpioIrqGpio21] = DT_INST_IRQ_BY_NAME(inst, gpio21, irq), \
              [kDtGpioIrqGpio22] = DT_INST_IRQ_BY_NAME(inst, gpio22, irq), \
              [kDtGpioIrqGpio23] = DT_INST_IRQ_BY_NAME(inst, gpio23, irq), \
              [kDtGpioIrqGpio24] = DT_INST_IRQ_BY_NAME(inst, gpio24, irq), \
              [kDtGpioIrqGpio25] = DT_INST_IRQ_BY_NAME(inst, gpio25, irq), \
              [kDtGpioIrqGpio26] = DT_INST_IRQ_BY_NAME(inst, gpio26, irq), \
              [kDtGpioIrqGpio27] = DT_INST_IRQ_BY_NAME(inst, gpio27, irq), \
              [kDtGpioIrqGpio28] = DT_INST_IRQ_BY_NAME(inst, gpio28, irq), \
              [kDtGpioIrqGpio29] = DT_INST_IRQ_BY_NAME(inst, gpio29, irq), \
              [kDtGpioIrqGpio30] = DT_INST_IRQ_BY_NAME(inst, gpio30, irq), \
              [kDtGpioIrqGpio31] = DT_INST_IRQ_BY_NAME(inst, gpio31, irq), \
          },                                                               \
  },

    DT_INST_FOREACH_STATUS_OKAY(DT_DEVICE_ENTRY)};

uint32_t dt_gpio_num_devices(void) {
  return DT_NUM_INST_STATUS_OKAY(DT_DRV_COMPAT);
}

int32_t dt_gpio_device_id(uint32_t dev_idx) {
  if (dev_idx < DT_NUM_INST_STATUS_OKAY(DT_DRV_COMPAT)) {
    return dev[dev_idx].id;
  }
  return -1;
}

uintptr_t dt_gpio_reg_addr(uint32_t dev_idx) {
  if (dev_idx < DT_NUM_INST_STATUS_OKAY(DT_DRV_COMPAT)) {
    return dev[dev_idx].reg_addr;
  }
  return 0;
}

int32_t dt_gpio_irq_id(uint32_t dev_idx, dt_gpio_irq_type_t irq_type) {
  if (dev_idx < DT_NUM_INST_STATUS_OKAY(DT_DRV_COMPAT) &&
      irq_type < kDtGpioIrqTypeCount) {
    return dev[dev_idx].irq[irq_type];
  }
  return -1;
}
