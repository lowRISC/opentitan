# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

foreach device_name, device_lib : sw_lib_arch_core_devices
  otp_img = custom_target(
    'otp_img_' + device_name + '.vmem',
    command: make_otp_img_command,
    depend_files: [make_otp_img_depend_files,],
    input: make_otp_img_inputs,
    output: 'otp_img_' + device_name + '.vmem',
    build_always_stale: true,
    build_by_default: true,
  )

  custom_target(
    'otp_img_export_' + device_name,
    command: export_target_command,
    depend_files: [export_target_depend_files,],
    input: [otp_img],
    output: 'otp_img_export_' + device_name,
    build_always_stale: true,
    build_by_default: true,
  )
endforeach
