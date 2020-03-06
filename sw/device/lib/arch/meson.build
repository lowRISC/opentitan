# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

sw_lib_arch_sim_dv = declare_dependency(
  link_with: static_library(
    'device_sim_dv',
    sources: ['device_sim_dv.c'],
  ),
)

sw_lib_arch_sim_verilator = declare_dependency(
  link_with: static_library(
    'device_sim_verilator',
    sources: ['device_sim_verilator.c'],
  ),
)

sw_lib_arch_fpga_nexysvideo = declare_dependency(
  link_with: static_library(
    'device_fpga_nexysvideo',
    sources: ['device_fpga_nexysvideo.c'],
  ),
)

# Devices that are considered "basic" or "generic", and which
# can run general purpose programs.
# Effectively, this is all devices that are not specialized DV
# testbenches.
sw_lib_arch_core_devices = {
  'sim_dv': sw_lib_arch_sim_dv,
  'sim_verilator': sw_lib_arch_sim_verilator,
  'fpga_nexysvideo': sw_lib_arch_fpga_nexysvideo,
}
