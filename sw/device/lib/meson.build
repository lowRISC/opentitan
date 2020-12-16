# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

subdir('base')
subdir('arch')
subdir('crt')
subdir('dif')
subdir('runtime')
subdir('testing')

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
    ]
  )
)

# AES library (sw_lib_aes)
sw_lib_aes = declare_dependency(
  link_with: static_library(
    'aes_ot',
    sources: [
      hw_ip_aes_reg_h,
      'aes.c',
    ],
    dependencies: [
      top_earlgrey,
    ]
  )
)

# HMAC library (sw_lib_hmac)
sw_lib_hmac = declare_dependency(
  link_with: static_library(
    'hmac_ot',
    sources: [
      hw_ip_hmac_reg_h,
      'hw_sha256.c',
      'hmac.c',
    ],
    dependencies: [
      sw_lib_mem,
      top_earlgrey,
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

# IRQ Handlers Library
#
# handler.c contains various definitions with weak linkage, for interrupt
# handler symbols referenced from riscv_crt.
#
# To override default handlers, implement the declarations in handler.h, and
# link to this library to pick up the other default definitions, if needed.
#
# If you are getting errors for functions beginning `handler_` when linking a
# device executable, it's likely because you forgot to link this library.
sw_lib_irq_handlers = declare_dependency(
  link_with: static_library(
    'irq_default_handlers_ot',
    sources: [
      'handler.c',
    ],
    dependencies: [
      sw_lib_runtime_log,
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
