# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# All tests added to this dictionary will result in build targets that have
# names starting `sw/device/tests/<test_name>`. They will not contain the
# subdirectory name, because the build targets are really declared at the bottom
# of this file, rather than in the subdirectories.
sw_tests = {
  # 'test_name': {
  #   'library': test_lib,
  #   'dv_frames': true/false, # (can be omitted, defaults to `false`)
  # },
}

subdir('dif')
subdir('rom_ext')
subdir('runtime')
subdir('sim_dv')
subdir('otbn')

aes_test_lib = declare_dependency(
  link_with: static_library(
    'aes_test_lib',
    sources: ['aes_test.c'],
    dependencies: [
      sw_lib_aes,
      sw_lib_runtime_log,
    ],
  ),
)
sw_tests += {
  'aes_test': {
    'library': aes_test_lib,
  }
}

flash_ctrl_test_lib = declare_dependency(
  link_with: static_library(
    'flash_ctrl_test_lib',
    sources: ['flash_ctrl_test.c'],
    dependencies: [
      sw_lib_mem,
      sw_lib_mmio,
      sw_lib_flash_ctrl,
      sw_lib_runtime_log,
    ],
  ),
)
sw_tests += {
  'flash_ctrl_test': {
    'library': flash_ctrl_test_lib,
  }
}

sha256_test_lib = declare_dependency(
  link_with: static_library(
    'sha256_test_lib',
    sources: ['sha256_test.c'],
    dependencies: [
      sw_lib_hmac,
      sw_lib_flash_ctrl,
      sw_lib_runtime_log,
    ],
  ),
)
sw_tests += {
  'sha256_test': {
    'library': sha256_test_lib,
  }
}

usbdev_test_lib = declare_dependency(
  link_with: static_library(
    'usbdev_test_lib',
    sources: ['usbdev_test.c'],
    dependencies: [
      sw_lib_usb,
      sw_lib_runtime_log,
    ],
  ),
)
sw_tests += {
  'usbdev_test': {
    'library': usbdev_test_lib,
  }
}

coverage_test_lib = declare_dependency(
  link_with: static_library(
    'coverage_test_lib',
    sources: ['coverage_test.c'],
    dependencies: [
      collect_coverage,
    ],
  ),
)
sw_tests += {
  'coverage_test': {
    'library': coverage_test_lib,
  }
}

pmp_smoketest_napot_lib = declare_dependency(
  link_with: static_library(
    'pmp_smoketest_napot_lib',
    sources: ['pmp_smoketest_napot.c'],
    dependencies: [
      sw_lib_irq,
      sw_lib_runtime_log,
      sw_lib_runtime_hart,
      sw_lib_runtime_pmp,
      sw_lib_testing_test_status,
    ],
  ),
)
sw_tests += {
  'pmp_smoketest_napot': {
    'library': pmp_smoketest_napot_lib,
  }
}

pmp_smoketest_tor_lib = declare_dependency(
  link_with: static_library(
    'pmp_smoketest_tor_lib',
    sources: ['pmp_smoketest_tor.c'],
    dependencies: [
      sw_lib_irq,
      sw_lib_runtime_log,
      sw_lib_runtime_hart,
      sw_lib_runtime_pmp,
      sw_lib_testing_test_status,
    ],
  ),
)
sw_tests += {
  'pmp_smoketest_tor': {
    'library': pmp_smoketest_tor_lib,
  }
}

foreach sw_test_name, sw_test_info : sw_tests
  foreach device_name, device_lib : sw_lib_arch_core_devices
    sw_test_elf = executable(
      sw_test_name + '_' + device_name,
      name_suffix: 'elf',
      dependencies: [
        riscv_crt,
        device_lib,
        sw_test_info['library'],
        sw_lib_irq_handlers,
        sw_lib_testing_test_main,
      ],
    )

    sw_test_embedded = custom_target(
      sw_test_name + '_' + device_name,
      command: make_embedded_target_command,
      depend_files: [make_embedded_target_depend_files,],
      input: sw_test_elf,
      output: make_embedded_target_outputs,
      build_by_default: true,
    )

    sw_test_sim_dv_frames = []
    if device_name == 'sim_dv' and \
        sw_test_info.has_key('dv_frames') and sw_test_info['dv_frames']
      sw_test_sim_dv_frames_bin = custom_target(
        sw_test_name + '_sim_dv_frames_bin',
        command: [
          spiflash_bin,
          '--input=@INPUT@',
          '--dump-frames=@OUTPUT@',
        ],
        input: sw_test_embedded[0],
        output: '@BASENAME@.frames.bin',
      )

      sw_test_sim_dv_frames_vmem = custom_target(
        sw_test_name + '_sim_dv_frames_vmem',
        command: [
          prog_srec_cat,
          '@INPUT@',
          '--binary',
          '--offset', '0x0',
          '--byte-swap', '4',
          '--fill', '0xff',
          '-within', '@INPUT@',
          '-binary',
          '-range-pad', '4',
          '--output', '@OUTPUT@',
          '--vmem',
        ],
        input: sw_test_sim_dv_frames_bin,
        output: '@BASENAME@.vmem',
      )
      sw_test_sim_dv_frames = [
        sw_test_sim_dv_frames_bin,
        sw_test_sim_dv_frames_vmem,
      ]
    endif

    sw_test_sim_dv_logs = []
    if device_name == 'sim_dv'
      sw_test_sim_dv_logs = custom_target(
        sw_test_name + '_sim_dv_logs',
        command: extract_sw_logs_sim_dv_command,
        depend_files: [extract_sw_logs_sim_dv_depend_files,],
        input: sw_test_elf,
        output: extract_sw_logs_sim_dv_outputs,
      )
    endif

    custom_target(
      sw_test_name + '_export_' + device_name,
      command: export_target_command,
      depend_files: [export_target_depend_files,],
      input: [
        sw_test_elf,
        sw_test_embedded,
        sw_test_sim_dv_frames,
        sw_test_sim_dv_logs,
      ],
      output: sw_test_name + '_export_' + device_name,
      build_always_stale: true,
      build_by_default: true,
    )
  endforeach
endforeach

# Specific custom configuration for `crt_test`
foreach device_name, device_lib : sw_lib_arch_core_devices
  crt_test_elf = executable(
    'crt_test_' + device_name,
    name_suffix: 'elf',
    sources: ['crt_test.c'],
    dependencies: [
      riscv_crt,
      device_lib,
      sw_lib_irq_handlers,
      sw_lib_testing_test_status,
      sw_lib_runtime_print,
      sw_lib_runtime_log,
      sw_lib_dif_uart,
      # Explicitly do not pull in the test main; we need to run right after
      # the CRT is done executing.
      # sw_lib_testing_test_main,
    ],
  )

  crt_test_embedded = custom_target(
    'crt_test_' + device_name,
    command: make_embedded_target_command,
    depend_files: [make_embedded_target_depend_files,],
    input: crt_test_elf,
    output: make_embedded_target_outputs,
    build_by_default: true,
  )

  custom_target(
    'crt_test_export_' + device_name,
    command: export_target_command,
    depend_files: [export_target_depend_files,],
    input: [crt_test_elf, crt_test_embedded],
    output: 'crt_test_export_' + device_name,
    build_always_stale: true,
    build_by_default: true,
  )
endforeach
