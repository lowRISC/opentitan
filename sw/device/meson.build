# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

subdir('lib')
subdir('exts')

# Arguments for custom_target, for converting a linked .elf file into .bin and .vmem
# files (plus a disassembled .dis file).
#
# These definitions should only be available to directories which define executables.
make_embedded_target_outputs = ['@BASENAME@.bin', '@BASENAME@.dis', '@BASENAME@.32.vmem', '@BASENAME@.64.vmem']
make_embedded_target_command = [
  prog_python,
  meson.source_root() / 'util/embedded_target.py',
  '--objcopy', prog_objcopy,
  '--srec_cat', prog_srec_cat,
  '--objdump', prog_objdump,
  '--input', '@INPUT@',
  '--basename', '@BASENAME@',
  '--outdir', '@OUTDIR@',
]
make_embedded_target_depend_files = [
  meson.source_root() / 'util/embedded_target.py',
]

embedded_target_extra_link_args = [
  '-Wl,--build-id=none',
]

# Generate the txt files (rodata sections and logs deconstructed from the elf) used by DV
# simulations.
extract_sw_logs_sim_dv_outputs = ['@BASENAME@.rodata.txt', '@BASENAME@.logs.txt']
extract_sw_logs_sim_dv_command = [
  prog_python, meson.source_root() / 'util/device_sw_utils/extract_sw_logs.py',
  '--elf-file', '@INPUT@',
  '--rodata-sections', '.rodata',
  '--logs-fields-section', '.logs.fields',
  '--name', '@BASENAME@',
  '--outdir', '@OUTDIR@',
]
extract_sw_logs_sim_dv_depend_files = [
  meson.source_root() / 'util/device_sw_utils/extract_sw_logs.py',
]

# Generates the OTP image containing root secrets, sw configuration partitions and
# the life cycle state.
# TODO: This just puts the device into RMA life cycle state, with randomized root keys.
# We are using RMA in order to open up all debug and functional infrastructure
# as our testing and emulation environments require that.
# Need to make this more flexible in the future.
# TODO: additional OTP partitions can be included with the --add-cfg switch
# see also util/design/README.md
make_otp_img_inputs = [meson.source_root() / 'hw/ip/otp_ctrl/data/otp_ctrl_img_rma.hjson']
make_otp_img_command = [
  prog_python, meson.source_root() / 'util/design/gen-otp-img.py',
  '--quiet',
  '--img-cfg', '@INPUT@',
  '--out', '@OUTPUT@',
]
make_otp_img_depend_files = [
  meson.source_root() / 'util/design/gen-otp-img.py',
]

# Generates a scrambled version of a ROM image from an ELF
#
# TODO: This is currently top_earlgrey-specific. That's fine for now, because
#       top_earlgrey is the only top-level with a rom_ctrl block, but we'll
#       need to make this more generic if we support more top-levels.
scramble_image_hjson = [
  meson.source_root() / 'hw/top_earlgrey/data/autogen/top_earlgrey.gen.hjson'
]
scramble_image_outputs = [
  '@BASENAME@.scr.40.vmem',
]
scramble_image_command = [
    prog_python,
    meson.source_root() / 'hw/ip/rom_ctrl/util/scramble_image.py',
    scramble_image_hjson,
    '@INPUT@',
    '@OUTPUT@',
]
scramble_image_depend_files = [
    meson.source_root() / 'hw/ip/rom_ctrl/util/scramble_image.py',
    scramble_image_hjson
]

subdir('boot_rom')
subdir('otp_img')
subdir('silicon_creator')
subdir('examples')
subdir('sca')
subdir('tests')
subdir('benchmarks')
subdir('tock')
subdir('riscv_compliance_support')
