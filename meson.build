# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

project('opentitan', 'c', 'cpp', version: '0.1',)

target = get_option('target')
if target == 'undef'
  error('target option not set. Please run meson with a valid build target option.')
endif

if target == 'verilator'
  # TODO: Consider using extra args array if using this flag globally is no
  # longer OK.
  add_project_arguments('-DSIMULATION', language: 'c')
endif

# The following flags are applied to all native builds.
add_project_arguments('-Wall', '-Werror', 'cpp_std=c++14', language: 'cpp')
add_project_arguments('-std=gnu99', '-Wall', '-Werror', language: 'c')

# Common program references.
prog_python = import('python').find_installation('python3')
prog_objcopy = find_program('objcopy')
prog_srec_cat = find_program('srec_cat')
prog_git = find_program('git')

# RISCV linker parameters.
riscv_linkfile = files(['sw/exts/common/link.ld'])
riscv_link_args = ['-Wl,-T,@0@/@1@'.format('..', riscv_linkfile[0])]
riscv_link_deps = [riscv_linkfile]

# RISCV CRT parameters
startup_files = files(['sw/exts/common/_crt.c'])

# Additional arguments for utility in charge of generating bin and vmem outputs
# These variables are expected to be used in custom_target rules.
embedded_target_output = ['@BASENAME@.bin', '@BASENAME@.vmem']
embedded_target_args = [prog_python, '../util/embedded_target.py',
  '--objcopy', prog_objcopy, '--srec_cat', prog_srec_cat,
  '--input', '@INPUT@', '--basename', '@BASENAME@', '--outdir', '@OUTDIR@']

# HW headers. Placed here to avoid adding meson build files in the hw directory.
gen_hw_hdr = generator(
  prog_python,
  output: '@BASENAME@_regs.h',
  arguments: [
    '@SOURCE_DIR@/util/regtool.py', '-D', '-o', '@BUILD_DIR@/@BASENAME@_regs.h',
    '@INPUT@',
  ],
)

# TODO: Considering moving these into hw/ip directories.
hw_ip_flash_ctrl_regs_h = gen_hw_hdr.process('hw/ip/flash_ctrl/doc/flash_ctrl.hjson')
hw_ip_gpio_reg_h = gen_hw_hdr.process('hw/ip/gpio/doc/gpio.hjson')
hw_ip_hmac_reg_h = gen_hw_hdr.process('hw/ip/hmac/doc/hmac.hjson')
hw_ip_spi_device_reg_h = gen_hw_hdr.process('hw/ip/spi_device/doc/spi_device.hjson')
hw_ip_rv_timer_reg_h = gen_hw_hdr.process('hw/ip/rv_timer/doc/rv_timer.hjson')
hw_ip_uart_reg_h = gen_hw_hdr.process('hw/ip/uart/doc/uart.hjson')
hw_ip_usbdev_reg_h = gen_hw_hdr.process('hw/ip/usbdev/doc/usbdev.hjson')

subdir('sw')
