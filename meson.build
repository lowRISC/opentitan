# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

project(
  'opentitan', 'c', 'cpp',
  version: '0.1',
  meson_version: '>=0.51.0', # Matches version in python-requirements.txt
  default_options: [
    'c_std=c11',
    'build.c_std=c11',
    'cpp_std=c++14',
    'build.cpp_std=c++14',
    'warning_level=1',
    'build.warning_level=1',
    'werror=true',
    'build.werror=true',
    'debug=true',
    'build.debug=true',
    'b_staticpic=false', # Disable PIC for device static libraries
    'b_pie=false',       # Disable PIE for device executables
  ],
)

target = get_option('target')
if target == 'undef'
  error('target option not set. Please run meson with a valid build target option.')
endif

ot_version = get_option('ot_version')
if ot_version == 'undef'
  error('ot_version option not set. Please run meson with a valid OpenTitan version option.')
endif

if target == 'sim-verilator'
  # TODO: Consider using extra args array if using this flag globally is no
  # longer OK.
  add_project_arguments('-DSIMULATION', language: 'c')
endif

dev_bin_dir = get_option('dev_bin_dir')
host_bin_dir = get_option('host_bin_dir')
if dev_bin_dir == 'undef' or host_bin_dir == 'undef'
  error('dev_bin_dir option not set. Please run meson with a valid binary directory option.')
endif

# C Arguments to optimize for size
optimize_size_args = [
  '-Os', # General "Optimize for Size" Option
  '-fvisibility=hidden', # Hide symbols by default
]

# The following flags are applied to *all* builds, both cross builds
# and native builds.
add_project_arguments(
  '-I' + meson.source_root(),
  '-I' + meson.build_root(),
  language: 'cpp', native: false)
add_project_arguments(
  '-I' + meson.source_root(),
  '-I' + meson.build_root(),
  language: 'cpp', native: true)

add_project_arguments(
  '-I' + meson.source_root(),
  '-I' + meson.build_root(),
  '-isystem' + meson.source_root() / 'sw/device/lib/base/freestanding',
  language: 'c', native: false)
add_project_arguments(
  '-I' + meson.source_root(),
  '-I' + meson.build_root(),
  language: 'c', native: true)

# The following flags are applied only to cross builds
add_project_arguments(
  # Do not use standard system startup files or libraries
  '-nostartfiles', '-nostdlib', '-nostdinc',
  '-static', # Only link static files
  optimize_size_args,
  language: 'cpp', native: false)
add_project_arguments(
  # Do not use standard system startup files or libraries
  '-nostartfiles', '-nostdlib', '-nostdinc',
  '-static', # Only link static files
  optimize_size_args,
  language: 'c', native: false)
add_project_link_arguments(
  '-nostdlib', # Do not use standard system startup files or libraries
  language: 'cpp', native: false)
add_project_link_arguments(
  '-nostdlib', # Do not use standard system startup files or libraries
  language: 'c', native: false)

# Common program references.
prog_python = import('python').find_installation('python3')
prog_objdump = find_program('objdump')
prog_objcopy = find_program('objcopy')
prog_srec_cat = find_program('srec_cat')
prog_git = find_program('git')

# Hardware register headers. These are generated from HJSON files, and accesible
# in C via |#include "{IP_NAME}_regs.h"|.
gen_hw_hdr = generator(
  prog_python,
  output: '@BASENAME@_regs.h',
  arguments: [
    '@SOURCE_DIR@/util/regtool.py', '-D', '-o', '@BUILD_DIR@/@BASENAME@_regs.h',
    '@INPUT@',
  ],
)

# TODO: Considering moving these into hw/ip directories.
hw_ip_aes_reg_h = gen_hw_hdr.process('hw/ip/aes/data/aes.hjson')
hw_ip_flash_ctrl_regs_h = gen_hw_hdr.process('hw/ip/flash_ctrl/data/flash_ctrl.hjson')
hw_ip_gpio_reg_h = gen_hw_hdr.process('hw/ip/gpio/data/gpio.hjson')
hw_ip_hmac_reg_h = gen_hw_hdr.process('hw/ip/hmac/data/hmac.hjson')
hw_ip_spi_device_reg_h = gen_hw_hdr.process('hw/ip/spi_device/data/spi_device.hjson')
hw_ip_rv_timer_reg_h = gen_hw_hdr.process('hw/ip/rv_timer/data/rv_timer.hjson')
hw_ip_uart_reg_h = gen_hw_hdr.process('hw/ip/uart/data/uart.hjson')
hw_ip_usbdev_reg_h = gen_hw_hdr.process('hw/ip/usbdev/data/usbdev.hjson')
hw_top_earlgrey_pinmux_h = gen_hw_hdr.process('hw/top_earlgrey/ip/pinmux/data/autogen/pinmux.hjson')

subdir('sw')
