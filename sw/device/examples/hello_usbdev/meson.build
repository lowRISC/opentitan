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
      device_lib,
      ottf_start_lib,
      sw_examples_demos,
      sw_lib_runtime_hart,
      sw_lib_pinmux,
      sw_lib_dif_pinmux,
      sw_lib_dif_gpio,
      sw_lib_irq,
      sw_lib_dif_spi_device,
      sw_lib_runtime_log,
      sw_lib_dif_uart,
      sw_lib_usb,
      sw_lib_testing_test_status,
    ],
  )

  target_name = 'hello_usbdev_@0@_' + device_name

  hello_usbdev_dis = custom_target(
    target_name.format('dis'),
    input: hello_usbdev_elf,
    kwargs: elf_to_dis_custom_target_args,
  )

  hello_usbdev_bin = custom_target(
    target_name.format('bin'),
    input: hello_usbdev_elf,
    kwargs: elf_to_bin_custom_target_args,
  )

  hello_usbdev_vmem32 = custom_target(
    target_name.format('vmem32'),
    input: hello_usbdev_bin,
    kwargs: bin_to_vmem32_custom_target_args,
  )

  hello_usbdev_vmem64 = custom_target(
    target_name.format('vmem64'),
    input: hello_usbdev_bin,
    kwargs: bin_to_vmem64_custom_target_args,
  )

  hello_usbdev_scr_vmem64 = custom_target(
    target_name.format('scrambled'),
    input: hello_usbdev_vmem64,
    output: flash_image_outputs,
    command: flash_image_command,
    depend_files: flash_image_depend_files,
    build_by_default: true,
  )

  custom_target(
    target_name.format('export'),
    command: export_target_command,
    depend_files: [export_target_depend_files,],
    input: [
      hello_usbdev_elf,
      hello_usbdev_dis,
      hello_usbdev_bin,
      hello_usbdev_vmem32,
      hello_usbdev_vmem64,
      hello_usbdev_scr_vmem64,
    ],
    output: target_name.format('export'),
    build_always_stale: true,
    build_by_default: true,
  )
endforeach
