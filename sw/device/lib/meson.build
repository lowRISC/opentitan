# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

subdir('base')
subdir('arch')
subdir('crt')
subdir('dif')
subdir('runtime')
subdir('crypto')

# Flash controller library (sw_lib_flash_ctrl)
sw_lib_flash_ctrl = declare_dependency(
  link_with: static_library(
    'flash_ctrl_ot',
    sources: [
      hw_ip_flash_ctrl_reg_h,
      'flash_ctrl.c',
    ],
    dependencies: [
      top_earlgrey,
    ]
  )
)

# Temp ibex peri library (sw_lib_ibex)
sw_lib_ibex = declare_dependency(
  link_with: static_library(
    'ibex_ot',
    sources: [
      hw_ip_ibex_reg_h,
      'ibex_peri.c',
    ],
    dependencies: [
      top_earlgrey,
    ]
  )
)

# PINMUX library (sw_lib_pinmux)
sw_lib_pinmux = declare_dependency(
  link_with: static_library(
    'pinmux_ot',
    sources: [
      hw_top_earlgrey_pinmux_reg_h,
      'pinmux.c',
    ],
    dependencies: [
      top_earlgrey,
      sw_lib_dif_pinmux,
    ]
  )
)

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
