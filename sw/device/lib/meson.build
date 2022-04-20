# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

subdir('base')
subdir('arch')
subdir('crt')
subdir('dif')
subdir('runtime')
subdir('crypto')

# Temp ibex peri library (sw_lib_ibex)
sw_lib_ibex = sw_lib_runtime_ibex

# IRQ library (sw_lib_irq)
sw_lib_irq = declare_dependency(
  link_with: static_library(
    'irq_ot',
    sources: [
      'irq.c',
    ],
  )
)

# USB DEV library (sw_lib_usb)
sw_lib_usb = declare_dependency(
  link_with: static_library(
    'usb_ot',
    sources: [
      hw_ip_usbdev_reg_h,
      'usb_controlep.c',
      'usb_simpleserial.c',
      'usbdev.c',
    ],
    dependencies: [
      top_earlgrey,
    ]
  )
)

subdir('testing')
