# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Dictionaries that can be used as `custom_target` arguments for common
# operations on `.elf` and `.bin` files. To create a custom target using
# `my_custom_target_args`:
#    my_var = custom_target(
#      my_target_name,
#      input: my_target_input,
#      kwargs: my_custom_target_args,
#    )

# `custom_target` arguments for creating a `.dis` file from an `.elf` file.
elf_to_dis_custom_target_args = {
  'output': '@BASENAME@.dis',
  'command': [
    prog_objdump,
    '--disassemble',
    '--headers',
    '--line-numbers',
    '--disassemble-zeroes',
    '--source',
    '@INPUT@',
  ],
  # Write the stdout of objdump to the output file.
  'capture': true,
  'build_by_default': true,
}

# `custom_target` arguments for creating a `.bin` file from an `.elf` file.
elf_to_bin_custom_target_args = {
  'output': '@BASENAME@.bin',
  'command': [
    prog_objcopy,
    '--output-target', 'binary',
    '@INPUT@',
    '@OUTPUT@',
  ],
  'build_by_default': true,
}

# Argument template for creating `.*.vmem` files from a `.elf` file.
# The arguments array for a particular word size can be built using:
# bin_to_vmem_args_template.format(num_words, num_bits).split(' ')
# Note: Joining an array to be able to comment individual arguments.
# TODO: Replace command for objcopy if endianess issues can be solved
# https://github.com/lowRISC/opentitan/issues/1107
bin_to_vmem_args_template = ' '.join([
    '@INPUT@',
    # Interpret input as binary.
    '--binary',
    # Reverse the endianness of every word.
    '--offset', '0x0', '--byte-swap', '@0@',
    # Pad to word alignment.
    '--fill', '0xff', '-within', '@INPUT@', '-binary', '-range-pad', '@0@',
    # Output a vmem file with specified word size
    '--output', '@OUTPUT@', '--vmem', '@1@',
])

# `custom_target` arguments for creating a `.32.vmem` file from a `.elf` file.
bin_to_vmem32_custom_target_args = {
  'output': '@BASENAME@.32.vmem',
  'command': [prog_srec_cat] + bin_to_vmem_args_template.format(4, 32).split(' '),
  'build_by_default': true,
}

# `custom_target` arguments for creating a `.64.vmem` file from a `.elf` file.
bin_to_vmem64_custom_target_args = {
  'output': '@BASENAME@.64.vmem',
  'command': [prog_srec_cat] + bin_to_vmem_args_template.format(8, 64).split(' '),
  'build_by_default': true,
}

embedded_target_extra_link_args = [
  '-Wl,--build-id=none',
]

# Generate the txt files (rodata sections and logs deconstructed from the elf) used by DV
# simulations.
extract_sw_logs_sim_dv_outputs = ['@BASENAME@.rodata.txt', '@BASENAME@.logs.txt']
extract_sw_logs_sim_dv_command = [
  prog_python, meson.project_source_root() / 'util/device_sw_utils/extract_sw_logs.py',
  '--elf-file', '@INPUT@',
  '--rodata-sections', '.rodata',
  '--logs-fields-section', '.logs.fields',
  '--name', '@BASENAME@',
  '--outdir', '@OUTDIR@',
]
extract_sw_logs_sim_dv_depend_files = [
  meson.project_source_root() / 'util/device_sw_utils/extract_sw_logs.py',
]

# Generates the OTP image containing root secrets, sw configuration partitions and
# the life cycle state.
# TODO: This just puts the device into RMA life cycle state, with randomized root keys.
# We are using RMA in order to open up all debug and functional infrastructure
# as our testing and emulation environments require that.
# Need to make this more flexible in the future.
# TODO: additional OTP partitions can be included with the --add-cfg switch
# see also util/design/README.md
make_otp_img_inputs = [meson.project_source_root() / 'hw/ip/otp_ctrl/data/otp_ctrl_img_rma.hjson']
make_otp_img_command = [
  prog_python, meson.project_source_root() / 'util/design/gen-otp-img.py',
  '--quiet',
  '--img-cfg', '@INPUT@',
  '--out', '@OUTPUT@',
]
make_otp_img_depend_files = [
  meson.project_source_root() / 'util/design/gen-otp-img.py',
]

# Generates a scrambled version of a ROM image from an ELF
#
# TODO: This is currently top_earlgrey-specific. That's fine for now, because
#       top_earlgrey is the only top-level with a rom_ctrl block, but we'll
#       need to make this more generic if we support more top-levels.
scramble_image_hjson = [
  meson.project_source_root() / 'hw/top_earlgrey/data/autogen/top_earlgrey.gen.hjson'
]
scramble_image_outputs = [
  '@BASENAME@.scr.39.vmem',
]
scramble_image_command = [
    prog_python,
    meson.project_source_root() / 'hw/ip/rom_ctrl/util/scramble_image.py',
    scramble_image_hjson,
    '@INPUT@',
    '@OUTPUT@',
]
scramble_image_depend_files = [
    meson.project_source_root() / 'hw/ip/rom_ctrl/util/scramble_image.py',
    scramble_image_hjson
]

# Generate proper flash image
#

flash_image_outputs = [
  '@BASENAME@.scr.vmem',
]

flash_image_command = [
    prog_python,
    meson.project_source_root() / 'util/design/gen-flash-img.py',
    '@INPUT@',
    '@OUTPUT@',
]

flash_image_depend_files = [
    meson.project_source_root() / 'util/design/gen-flash-img.py',
]


# Signing keys for ROM_EXT images.
signing_keys = {
  'test_key_0': {
    'path': meson.project_source_root() / 'sw/device/silicon_creator/mask_rom/keys/test_key_0_rsa_3072_exp_f4.der',
  },
}

subdir('lib')
subdir('otp_img')
subdir('silicon_creator')
subdir('silicon_owner')
subdir('examples')
subdir('sca')
subdir('tests')
subdir('benchmarks')
subdir('riscv_compliance_support')
