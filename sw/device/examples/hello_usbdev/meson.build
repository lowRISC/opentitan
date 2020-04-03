# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

foreach device_name, device_lib : sw_lib_arch_core_devices
  hello_usbdev_elf = executable(
    'hello_usbdev_' + device_name,
    sources: [
      hw_ip_usbdev_reg_h,
      'hello_usbdev.c',
    ],
    name_suffix: 'elf',
    dependencies: [
      sw_examples_demos,
      sw_lib_runtime_hart,
      sw_lib_pinmux,
      sw_lib_dif_gpio,
      sw_lib_irq,
      sw_lib_spi_device,
      sw_lib_uart,
      sw_lib_base_log,
      sw_lib_usb,
      riscv_crt,
      sw_lib_irq_handlers,
      device_lib,
    ],
  )

  hello_usbdev_embedded = custom_target(
    'hello_usbdev_' + device_name,
    command: make_embedded_target,
    input: hello_usbdev_elf,
    output: make_embedded_target_outputs,
    build_by_default: true,
  )

  custom_target(
    'hello_usbdev_export_' + device_name,
    command: export_embedded_target,
    input: [hello_usbdev_elf, hello_usbdev_embedded],
    output: 'hello_usbdev_export_' + device_name,
    build_always_stale: true,
    build_by_default: true,
  )
endforeach
