# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# All build targets below in `sw_tests` or `sw_signed_tests` will have names
# starting with `sw/device/tests/<test_name>`. They will not contain the
# subdirectory name (e.g., `sim_dv/`), because the build targets are really
# declared in the for loops in this build file.

# All tests added to the `sw_test` dictionary will be compiled for various
# device platforms (DV, Verilator, and FPGA). Additionally there are several
# build options that can be configured for each test, all of which default to
# `false`. These include:
#  - whether or not to produce SPI flash frames of the test image for
#    bootstrap test purposes.
#  - whether or not to produce signed images for this test, enabling the test
#    to be run by either the test or mask ROMs.
#  - whether or not to launch the test from the OTTF, or to run it directly
#    after the OTTF initialization assembly (`ottf_start.S`) runs.
sw_tests = {
  # 'test_name': {
  #   'library':          test_lib,
  #   'dv_frames':        true/false, # (can be omitted, defaults to `false`)
  #   'sign':             true/false, # (can be omitted, defaults to `false`)
  #   'ottf_start_only':  true/false, # (can be omitted, defaults to `false`)
  #   'run_at_rom_stage': true/false, # (can be omitted, defaults to `false`)
  # },
}

###############################################################################
# Example Chip-Level Tests
###############################################################################
# Most chip-level tests run at the flash stage. These can rely on the OTTF to
# provide common HW initialization (e.g., pinmux, UART, flash, IRQ vector).
example_test_from_flash_lib = declare_dependency(
  link_with: static_library(
    'example_test_from_flash_lib ',
    sources: ['example_test_from_flash.c'],
    dependencies: [
      # Add dependencies here.
    ],
  ),
)
sw_tests += {
  'example_test_from_flash': {
    'library': example_test_from_flash_lib,
  }
}

# A few chip-level tests need to run at the ROM stage. These may not rely on the
# OTTF, and therefore must do all required initializations within the test.
example_test_from_rom_lib = declare_dependency(
  link_with: static_library(
    'example_test_from_rom_lib',
    sources: [
      'example_test_from_rom.c',
    ],
    dependencies: [
      sw_lib_dif_uart,
      sw_lib_mmio,
      sw_lib_pinmux,
      sw_lib_runtime_hart,
      sw_lib_runtime_print,
      sw_lib_runtime_log,
      sw_lib_testing_test_status,
    ],
  ),
)
sw_tests += {
  'example_test_from_rom': {
    'library': example_test_from_rom_lib,
    'run_at_rom_stage': true,
  }
}

###############################################################################
# Cryptolib Tests
###############################################################################
subdir('crypto')

###############################################################################
# Smoke Tests
###############################################################################
rv_plic_smoketest_lib = declare_dependency(
  link_with: static_library(
    'rv_plic_smoketest_lib',
    sources: ['rv_plic_smoketest.c'],
    dependencies: [
      sw_lib_dif_uart,
      sw_lib_dif_rv_plic,
      sw_lib_irq,
      sw_lib_mmio,
      sw_lib_runtime_log,
      sw_lib_runtime_hart,
      sw_lib_testing_test_status,
      top_earlgrey,
    ],
  ),
)
sw_tests += {
  'rv_plic_smoketest': {
    'library': rv_plic_smoketest_lib,
  }
}

uart_smoketest_lib = declare_dependency(
  link_with: static_library(
    'uart_smoketest_lib',
    sources: ['uart_smoketest.c'],
    dependencies: [
      sw_lib_dif_uart,
      sw_lib_mmio,
      sw_lib_runtime_hart,
    ],
  ),
)
sw_tests += {
  'uart_smoketest': {
    'library': uart_smoketest_lib,
    'sign': true,
  }
}

rv_timer_smoketest_lib = declare_dependency(
  link_with: static_library(
    'rv_timer_smoketest_lib',
    sources: ['rv_timer_smoketest.c'],
    dependencies: [
      sw_lib_dif_rv_timer,
      sw_lib_runtime_log,
      sw_lib_mmio,
      sw_lib_runtime_hart,
      sw_lib_irq,
    ],
  ),
)
sw_tests += {
  'rv_timer_smoketest': {
    'library': rv_timer_smoketest_lib,
  }
}

hmac_smoketest_lib = declare_dependency(
  link_with: static_library(
    'hmac_smoketest_lib',
    sources: ['hmac_smoketest.c'],
    dependencies: [
      sw_lib_dif_hmac,
      sw_lib_mmio,
      sw_lib_runtime_hart,
      sw_lib_runtime_log,
      sw_lib_testing_hmac_testutils,
    ],
  ),
)
sw_tests += {
  'hmac_smoketest': {
    'library': hmac_smoketest_lib,
  }
}

kmac_smoketest_lib = declare_dependency(
  link_with: static_library(
    'kmac_smoketest_lib',
    sources: ['kmac_smoketest.c'],
    dependencies: [
      sw_lib_dif_kmac,
      sw_lib_runtime_log,
      sw_lib_mmio,
      sw_lib_runtime_hart,
    ],
  ),
)
sw_tests += {
  'kmac_smoketest': {
    'library': kmac_smoketest_lib,
  }
}

rstmgr_smoketest_lib = declare_dependency(
  link_with: static_library(
    'rstmgr_smoketest_lib',
    sources: ['rstmgr_smoketest.c'],
    dependencies: [
      sw_lib_dif_rstmgr,
      sw_lib_mmio,
      sw_lib_runtime_hart,
      sw_lib_testing_rstmgr_testutils,
    ],
  ),
)
sw_tests += {
  'rstmgr_smoketest': {
    'library': rstmgr_smoketest_lib,
  }
}

rstmgr_sw_req_test_lib = declare_dependency(
  link_with: static_library(
    'rstmgr_sw_req_lib',
    sources: ['rstmgr_sw_req_test.c'],
    dependencies: [
      sw_lib_dif_rstmgr,
      sw_lib_mmio,
      sw_lib_runtime_hart,
    ],
  ),
)
sw_tests += {
  'rstmgr_sw_req_test': {
    'library': rstmgr_sw_req_test_lib,
  }
}

rstmgr_sw_rst_ctrl_test_lib = declare_dependency(
  link_with: static_library(
    'rstmgr_sw_rst_ctrl_test_lib',
    sources: [
      hw_ip_spi_host_reg_h,
      hw_ip_spi_device_reg_h,
      hw_ip_usbdev_reg_h,
      hw_ip_i2c_reg_h,
      'rstmgr_sw_rst_ctrl_test.c'],
    dependencies: [
      sw_lib_dif_rstmgr,
      sw_lib_dif_spi_device,
      sw_lib_dif_spi_host,
      sw_lib_dif_usbdev,
      sw_lib_dif_i2c,
      sw_lib_mmio,
      sw_lib_runtime_hart,
    ],
  ),
)
sw_tests += {
  'rstmgr_sw_rst_ctrl_test': {
    'library': rstmgr_sw_rst_ctrl_test_lib,
  }
}

otbn_smoketest_lib = declare_dependency(
  link_with: static_library(
    'otbn_smoketest_lib',
    sources: ['otbn_smoketest.c'],
    dependencies: [
      sw_lib_testing_entropy_testutils,
      sw_lib_dif_otbn,
      sw_lib_runtime_hart,
      sw_lib_runtime_otbn,
      top_earlgrey,
      sw_otbn['barrett384']['rv32embed_dependency'],
      sw_otbn['err_test']['rv32embed_dependency'],
    ],
  ),
)
sw_tests += {
  'otbn_smoketest': {
    'library': otbn_smoketest_lib,
  }
}

otp_ctrl_smoketest_lib = declare_dependency(
  link_with: static_library(
    'otp_ctrl_smoketest_lib',
    sources: ['otp_ctrl_smoketest.c'],
    dependencies: [
      sw_lib_dif_otp_ctrl,
      sw_lib_runtime_log,
      sw_lib_mmio,
      sw_lib_runtime_hart,
      sw_lib_testing_otp_ctrl_testutils,
    ],
  ),
)
sw_tests += {
  'otp_ctrl_smoketest': {
    'library': otp_ctrl_smoketest_lib,
  }
}

gpio_smoketest_lib = declare_dependency(
  link_with: static_library(
    'gpio_smoketest_lib',
    sources: ['gpio_smoketest.c'],
    dependencies: [
      sw_lib_dif_gpio,
      sw_lib_mmio,
      sw_lib_runtime_log,
    ],
  ),
)
sw_tests += {
  'gpio_smoketest': {
    'library': gpio_smoketest_lib,
  }
}

if TOPNAME == 'top_earlgrey'
  aes_smoketest_lib_earlgrey_deps = [
    sw_lib_testing_entropy_testutils,
  ]
else
  aes_smoketest_lib_earlgrey_deps = []
endif

aes_smoketest_lib = declare_dependency(
  link_with: static_library(
    'aes_smoketest_lib',
    sources: ['aes_smoketest.c'],
    dependencies: [
      sw_lib_dif_aes,
      sw_lib_mmio,
      sw_lib_runtime_log,
      sw_lib_testing_aes_testutils,
      sw_lib_testing_test_status,
    ] + aes_smoketest_lib_earlgrey_deps,
  ),
)
sw_tests += {
  'aes_smoketest': {
    'library': aes_smoketest_lib,
  }
}

aes_idle_test_lib = declare_dependency(
  link_with: static_library(
    'aes_idle_test_lib',
    sources: ['aes_idle_test.c'],
    dependencies: [
      sw_lib_dif_aes,
      sw_lib_mmio,
      sw_lib_runtime_log,
      sw_lib_testing_entropy_testutils,
      sw_lib_testing_aes_testutils,
      sw_lib_testing_clkmgr_testutils,
      sw_lib_testing_test_status,
    ],
  ),
)
sw_tests += {
  'aes_idle_test': {
    'library': aes_idle_test_lib,
  }
}

clkmgr_smoketest_lib = declare_dependency(
  link_with: static_library(
    'clkmgr_smoketest_lib',
    sources: ['clkmgr_smoketest.c'],
    dependencies: [
      sw_lib_dif_clkmgr,
      sw_lib_mmio,
      sw_lib_runtime_log,
    ],
  ),
)
sw_tests += {
  'clkmgr_smoketest': {
    'library': clkmgr_smoketest_lib,
  }
}

clkmgr_off_peri_test_lib = declare_dependency(
  link_with: static_library(
    'clkmgr_off_peri_test_lib',
    sources: ['clkmgr_off_peri_test.c'],
    dependencies: [
      sw_lib_dif_aon_timer,
      sw_lib_dif_clkmgr,
      sw_lib_dif_pwrmgr,
      sw_lib_dif_rstmgr,
      sw_lib_dif_uart,
      sw_lib_mmio,
      sw_lib_runtime_log,
      sw_lib_runtime_ibex,
      sw_lib_testing_aon_timer_testutils,
      sw_lib_testing_rstmgr_testutils,
      top_earlgrey,
    ],
  ),
)
sw_tests += {
  'clkmgr_off_peri_test': {
    'library': clkmgr_off_peri_test_lib,
  }
}

clkmgr_external_clk_src_for_sw_test_lib = declare_dependency(
  link_with: static_library(
    'clkmgr_external_clk_src_for_sw_test_lib',
    sources: ['clkmgr_external_clk_src_for_sw_test.c'],
    dependencies: [
      sw_lib_dif_clkmgr,
      sw_lib_mmio,
      sw_lib_runtime_hart,
      sw_lib_runtime_ibex,
      sw_lib_runtime_log,
      sw_lib_testing_clkmgr_testutils,
      top_earlgrey,
    ],
  ),
)
sw_tests += {
  'clkmgr_external_clk_src_for_sw_test': {
    'library': clkmgr_external_clk_src_for_sw_test_lib,
  }
}

clkmgr_jitter_test_lib = declare_dependency(
  link_with: static_library(
    'clkmgr_jitter_test_lib',
    sources: ['clkmgr_jitter_test.c'],
    dependencies: [
      sw_lib_dif_clkmgr,
      sw_lib_mmio,
      sw_lib_runtime_log,
    ],
  ),
)
sw_tests += {
  'clkmgr_jitter_test': {
    'library': clkmgr_jitter_test_lib,
  }
}

csrng_smoketest_lib = declare_dependency(
  link_with: static_library(
    'csrng_smoketest_lib',
    sources: ['csrng_smoketest.c'],
    dependencies: [
      sw_lib_dif_csrng,
      sw_lib_mmio,
      sw_lib_runtime_log,
    ],
  ),
)
sw_tests += {
  'csrng_smoketest': {
    'library': csrng_smoketest_lib,
  }
}

entropy_src_fw_ovr_test_lib = declare_dependency(
  link_with: static_library(
    'entropy_src_fw_ovr_test_lib',
    sources: ['entropy_src_fw_ovr_test.c'],
    dependencies: [
      sw_lib_dif_entropy_src,
      sw_lib_mmio,
      sw_lib_runtime_log,
    ],
  ),
)
sw_tests += {
  'entropy_src_fw_ovr_test': {
    'library': entropy_src_fw_ovr_test_lib,
  }
}

entropy_src_smoketest_lib = declare_dependency(
  link_with: static_library(
    'entropy_src_smoketest_lib',
    sources: ['entropy_src_smoketest.c'],
    dependencies: [
      sw_lib_dif_entropy_src,
      sw_lib_mmio,
      sw_lib_runtime_log,
    ],
  ),
)
sw_tests += {
  'entropy_src_smoketest': {
    'library': entropy_src_smoketest_lib,
  }
}

aon_timer_smoketest_lib = declare_dependency(
  link_with: static_library(
    'aon_timer_smoketest_lib',
    sources: ['aon_timer_smoketest.c'],
    dependencies: [
      sw_lib_dif_aon_timer,
      sw_lib_testing_aon_timer_testutils,
      sw_lib_mmio,
      sw_lib_runtime_log,
    ],
  ),
)
sw_tests += {
  'aon_timer_smoketest': {
    'library': aon_timer_smoketest_lib,
  }
}

pwrmgr_smoketest_lib = declare_dependency(
  link_with: static_library(
    'pwrmgr_smoketest_lib',
    sources: ['pwrmgr_smoketest.c'],
    dependencies: [
      sw_lib_dif_aon_timer,
      sw_lib_dif_pwrmgr,
      sw_lib_dif_rstmgr,
      sw_lib_mmio,
      sw_lib_runtime_log,
      sw_lib_testing_aon_timer_testutils,
      sw_lib_testing_pwrmgr_testutils,
      sw_lib_testing_rstmgr_testutils,
    ],
  ),
)
sw_tests += {
  'pwrmgr_smoketest': {
    'library': pwrmgr_smoketest_lib,
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

sram_ctrl_smoketest_lib = declare_dependency(
  link_with: static_library(
    'sram_ctrl_smoketest_lib',
    sources: ['sram_ctrl_smoketest.c'],
    dependencies: [
      sw_lib_dif_sram_ctrl,
      sw_lib_runtime_log,
      sw_lib_mmio,
    ],
  ),
)
sw_tests += {
  'sram_ctrl_smoketest': {
    'library': sram_ctrl_smoketest_lib,
  }
}

###############################################################################
# IP Integration Tests
###############################################################################
# Flash Controller Tests
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

flash_ctrl_idle_low_power_test_lib = declare_dependency(
  link_with: static_library(
    'flash_ctrl_idle_low_power_test_lib',
    sources: ['flash_ctrl_idle_low_power_test.c'],
    dependencies: [
      sw_lib_mmio,
      sw_lib_dif_rstmgr,
      sw_lib_dif_pwrmgr,
      sw_lib_dif_aon_timer,
      sw_lib_dif_flash_ctrl,
      sw_lib_dif_rv_plic,
      sw_lib_testing_flash_ctrl_testutils,
      sw_lib_testing_isr_testutils,
      sw_lib_testing_pwrmgr_testutils,
      sw_lib_testing_rand_testutils,
      sw_lib_runtime_log,
      top_earlgrey,
    ],
  ),
)
sw_tests += {
  'flash_ctrl_idle_low_power_test': {
    'library': flash_ctrl_idle_low_power_test_lib,
  }
}

flash_ctrl_ops_test_lib = declare_dependency(
  link_with: static_library(
    'flash_ctrl_ops_test_lib',
    sources: ['flash_ctrl_ops_test.c'],
    dependencies: [
      sw_lib_mmio,
      sw_lib_dif_flash_ctrl,
      sw_lib_dif_rv_plic,
      sw_lib_testing_flash_ctrl_testutils,
      sw_lib_testing_isr_testutils,
      sw_lib_testing_rv_plic_testutils,
      sw_lib_runtime_log,
      top_earlgrey,
    ],
  ),
)
sw_tests += {
  'flash_ctrl_ops_test': {
    'library': flash_ctrl_ops_test_lib,
  }
}

# KMAC Tests
kmac_mode_kmac_test_lib = declare_dependency(
  link_with: static_library(
    'kmac_mode_kmac_test_lib',
    sources: ['kmac_mode_kmac_test.c'],
    dependencies: [
      sw_lib_dif_kmac,
      sw_lib_runtime_log,
      sw_lib_mmio,
      sw_lib_runtime_hart,
    ],
  ),
)
sw_tests += {
  'kmac_mode_kmac_test': {
    'library': kmac_mode_kmac_test_lib,
  }
}

kmac_mode_cshake_test_lib = declare_dependency(
  link_with: static_library(
    'kmac_mode_cshake_test_lib',
    sources: ['kmac_mode_cshake_test.c'],
    dependencies: [
      sw_lib_dif_kmac,
      sw_lib_runtime_log,
      sw_lib_mmio,
      sw_lib_runtime_hart,
    ],
  ),
)
sw_tests += {
  'kmac_mode_cshake_test': {
    'library': kmac_mode_cshake_test_lib,
  }
}

kmac_app_rom_test_lib = declare_dependency(
  link_with: static_library(
    'kmac_app_rom_test_lib',
    sources: [
      hw_ip_rom_ctrl_reg_h,
      'kmac_app_rom_test.c',
    ],
    dependencies: [
      sw_lib_dif_rom_ctrl,
      sw_lib_runtime_log,
      sw_lib_mmio,
    ],
  ),
)
sw_tests += {
  'kmac_app_rom_test': {
    'library': kmac_app_rom_test_lib,
  }
}

kmac_idle_test_lib = declare_dependency(
  link_with: static_library(
    'kmac_idle_test_lib',
    sources: ['kmac_idle_test.c'],
    dependencies: [
      sw_lib_dif_kmac,
      sw_lib_dif_clkmgr,
      sw_lib_runtime_log,
      sw_lib_mmio,
    ],
  ),
)
sw_tests += {
  'kmac_idle_test': {
    'library': kmac_idle_test_lib,
  }
}

# Lifecycle Controller Tests
lc_ctrl_otp_hw_cfg_test_lib = declare_dependency(
  link_with: static_library(
    'lc_ctrl_otp_hw_cfg_test_lib',
    sources: [
      'lc_ctrl_otp_hw_cfg_test.c',
    ],
    dependencies: [
      sw_lib_dif_lc_ctrl,
      sw_lib_dif_otp_ctrl,
      sw_lib_runtime_log,
      sw_lib_mmio,
      sw_lib_runtime_hart,
      sw_lib_testing_otp_ctrl_testutils,
    ],
  ),
)
sw_tests += {
  'lc_ctrl_otp_hw_cfg_test': {
    'library': lc_ctrl_otp_hw_cfg_test_lib,
  }
}

# OTBN Tests
otbn_rsa_test_lib = declare_dependency(
  link_with: static_library(
    'otbn_rsa_test_lib',
    sources: ['otbn_rsa_test.c'],
    dependencies: [
      sw_lib_testing_entropy_testutils,
      sw_lib_runtime_otbn,
      sw_lib_runtime_log,
      sw_lib_runtime_ibex,
      top_earlgrey,
      sw_otbn['rsa']['rv32embed_dependency'],
    ],
  ),
)
sw_tests += {
  'otbn_rsa_test': {
    'library': otbn_rsa_test_lib
  }
}

otbn_ecdsa_op_irq_test_lib = declare_dependency(
  link_with: static_library(
    'otbn_ecdsa_op_irq_test_lib',
    sources: ['otbn_ecdsa_op_irq_test.c'],
    dependencies: [
      sw_lib_testing_entropy_testutils,
      sw_lib_dif_rv_plic,
      sw_lib_runtime_otbn,
      sw_lib_runtime_log,
      sw_lib_runtime_ibex,
      top_earlgrey,
      sw_otbn['p256_ecdsa']['rv32embed_dependency'],
    ],
  ),
)
sw_tests += {
  'otbn_ecdsa_op_irq_test': {
    'library': otbn_ecdsa_op_irq_test_lib
  }
}

otbn_randomness_test_lib = declare_dependency(
  link_with: static_library(
    'otbn_randomness_test_lib',
    sources: ['otbn_randomness_test.c'],
    dependencies: [
      sw_lib_testing_entropy_testutils,
      sw_lib_dif_clkmgr,
      sw_lib_dif_rv_plic,
      sw_lib_runtime_otbn,
      sw_lib_runtime_log,
      sw_lib_runtime_ibex,
      top_earlgrey,
      sw_otbn['randomness']['rv32embed_dependency'],
    ],
  ),
)
sw_tests += {
  'otbn_randomness_test': {
    'library': otbn_randomness_test_lib
  }
}

otbn_mem_scramble_test_lib = declare_dependency(
  link_with: static_library(
    'otbn_mem_scramble_test_lib',
    sources: ['otbn_mem_scramble_test.c'],
    dependencies: [
      sw_lib_runtime_otbn,
      sw_lib_runtime_log,
      top_earlgrey,
      sw_otbn['randomness']['rv32embed_dependency'],
    ],
  ),
)
sw_tests += {
  'otbn_mem_scramble_test': {
    'library': otbn_mem_scramble_test_lib
  }
}

otbn_irq_test_lib = declare_dependency(
  link_with: static_library(
    'otbn_irq_test_lib',
    sources: ['otbn_irq_test.c'],
    dependencies: [
      sw_lib_testing_entropy_testutils,
      sw_lib_dif_otbn,
      sw_lib_dif_rv_plic,
      sw_lib_runtime_hart,
      sw_lib_runtime_otbn,
      top_earlgrey,
      sw_otbn['err_test']['rv32embed_dependency'],
    ],
  ),
)
sw_tests += {
  'otbn_irq_test': {
    'library': otbn_irq_test_lib,
  }
}

# USB Device Tests
usbdev_test_lib = declare_dependency(
  link_with: static_library(
    'usbdev_test_lib',
    sources: ['usbdev_test.c'],
    dependencies: [
      sw_lib_usb,
      sw_lib_dif_pinmux,
      sw_lib_pinmux,
      sw_lib_runtime_log,
    ],
  ),
)
sw_tests += {
  'usbdev_test': {
    'library': usbdev_test_lib,
  }
}

# SRAM Controller execution from Ret SRAM test.
sram_ctrl_execution_test_ret_lib = declare_dependency(
  link_with: static_library(
    'sram_ctrl_execution_test_ret_lib',
    sources: ['sram_ctrl_execution_test_ret.c'],
    dependencies: [
      sw_lib_dif_sram_ctrl,
      sw_lib_runtime_ibex,
      sw_lib_runtime_log,
      sw_lib_testing_sram_ctrl_testutils,
      top_earlgrey,
    ],
  ),
)
sw_tests += {
  'sram_ctrl_execution_test_ret': {
    'library': sram_ctrl_execution_test_ret_lib,
  }
}

# SRAM Controller low power retention SRAM contents test.
sram_ctrl_sleep_sram_ret_contents_test_lib = declare_dependency(
  link_with: static_library(
    'sram_ctrl_sleep_sram_ret_contents_test_lib',
    sources: ['sram_ctrl_sleep_sram_ret_contents_test.c'],
    dependencies: [
      sw_lib_mmio,
      sw_lib_dif_aon_timer,
      sw_lib_dif_pwrmgr,
      sw_lib_dif_rstmgr,
      sw_lib_testing_aon_timer_testutils,
      sw_lib_testing_pwrmgr_testutils,
      sw_lib_testing_rstmgr_testutils,
      sw_lib_runtime_log,
      top_earlgrey,
    ],
  ),
)
sw_tests += {
  'sram_ctrl_sleep_sram_ret_contents_test': {
    'library': sram_ctrl_sleep_sram_ret_contents_test_lib,
  }
}

# AON Timer irq test.
aon_timer_irq_test = declare_dependency(
  link_with: static_library(
    'aon_timer_irq_test',
    sources: [
      hw_ip_rstmgr_reg_h,
      'aon_timer_irq_test.c',
    ],
    dependencies: [
      sw_lib_dif_rstmgr,
      sw_lib_dif_aon_timer,
      sw_lib_dif_rv_timer,
      sw_lib_dif_rv_plic,
      sw_lib_runtime_log,
      sw_lib_runtime_ibex,
      sw_lib_testing_aon_timer_testutils,
      sw_lib_testing_rstmgr_testutils,
      sw_lib_testing_rv_plic_testutils,
      top_earlgrey,
    ],
  ),
)
sw_tests += {
  'aon_timer_irq_test': {
    'library': aon_timer_irq_test,
  }
}

# AON Timer wdog bite reset test.
aon_timer_wdog_bite_reset_test = declare_dependency(
  link_with: static_library(
    'aon_timer_wdog_bite_reset_test',
    sources: [
      hw_ip_rstmgr_reg_h,
      'aon_timer_wdog_bite_reset_test.c',
    ],
    dependencies: [
      sw_lib_dif_rstmgr,
      sw_lib_dif_aon_timer,
      sw_lib_dif_pwrmgr,
      sw_lib_runtime_log,
      sw_lib_testing_aon_timer_testutils,
      sw_lib_testing_rstmgr_testutils,
      sw_lib_testing_pwrmgr_testutils,
      top_earlgrey,
    ],
  ),
)
sw_tests += {
  'aon_timer_wdog_bite_reset_test': {
    'library': aon_timer_wdog_bite_reset_test,
  }
}

# AON Timer sleep wdog sleep pause test.
aon_timer_sleep_wdog_sleep_pause_test = declare_dependency(
  link_with: static_library(
    'aon_timer_sleep_wdog_sleep_pause_test',
    sources: [
      hw_ip_rstmgr_reg_h,
      'aon_timer_sleep_wdog_sleep_pause_test.c',
    ],
    dependencies: [
      sw_lib_dif_rstmgr,
      sw_lib_dif_aon_timer,
      sw_lib_dif_pwrmgr,
      sw_lib_runtime_log,
      sw_lib_testing_aon_timer_testutils,
      sw_lib_testing_rstmgr_testutils,
      sw_lib_testing_pwrmgr_testutils,
      top_earlgrey,
    ],
  ),
)
sw_tests += {
  'aon_timer_sleep_wdog_sleep_pause_test': {
    'library': aon_timer_sleep_wdog_sleep_pause_test,
  }
}

#PWM test
sleep_pwm_pulses_test_lib = declare_dependency(
  link_with: static_library(
    'sleep_pwm_pulses_test_lib',
    sources: [
      hw_top_earlgrey_pinmux_reg_h,
      hw_ip_pwm_reg_h,
      'sleep_pwm_pulses_test.c'],
    dependencies: [
      sw_lib_dif_aon_timer,
      sw_lib_dif_pwrmgr,
      sw_lib_dif_rstmgr,
      sw_lib_dif_pwm,
      sw_lib_dif_pinmux,
      sw_lib_mmio,
      sw_lib_runtime_log,
      sw_lib_testing_aon_timer_testutils,
      sw_lib_testing_pwrmgr_testutils,
      sw_lib_testing_rstmgr_testutils,
    ],
  ),
)
sw_tests += {
  'sleep_pwm_pulses_test': {
    'library': sleep_pwm_pulses_test_lib,
  }
}

# AON Timer wdog lc escalate test.
aon_timer_wdog_lc_escalate_test = declare_dependency(
  link_with: static_library(
    'aon_timer_wdog_lc_escalate_test',
    sources: [
      hw_ip_rstmgr_reg_h,
      'aon_timer_wdog_lc_escalate_test.c',
    ],
    dependencies: [
      sw_lib_dif_rstmgr,
      sw_lib_dif_aon_timer,
      sw_lib_dif_alert_handler,
      sw_lib_dif_pwrmgr,
      sw_lib_dif_rv_plic,
      sw_lib_runtime_log,
      sw_lib_runtime_ibex,
      sw_lib_testing_aon_timer_testutils,
      sw_lib_testing_alert_handler_testutils,
      sw_lib_testing_rstmgr_testutils,
      sw_lib_testing_rv_plic_testutils,
      top_earlgrey,
    ],
  ),
)
sw_tests += {
  'aon_timer_wdog_lc_escalate_test': {
    'library': aon_timer_wdog_lc_escalate_test,
  }
}

hmac_enc_irq_test_lib = declare_dependency(
  link_with: static_library(
    'hmac_enc_irq_test_lib',
    sources: ['hmac_enc_irq_test.c'],
    dependencies: [
      sw_lib_dif_hmac,
      sw_lib_dif_rv_plic,
      sw_lib_irq,
      sw_lib_mmio,
      sw_lib_runtime_ibex,
      sw_lib_runtime_log,
      sw_lib_testing_hmac_testutils,
      sw_lib_testing_isr_testutils,
      sw_lib_testing_rv_plic_testutils,
      top_earlgrey,
    ],
  ),
)
sw_tests += {
  'hmac_enc_irq_test': {
    'library': hmac_enc_irq_test_lib,
  }
}

hmac_enc_test_lib = declare_dependency(
  link_with: static_library(
    'hmac_enc_test_lib',
    sources: ['hmac_enc_test.c'],
    dependencies: [
      sw_lib_dif_hmac,
      sw_lib_mmio,
      sw_lib_runtime_log,
      sw_lib_testing_hmac_testutils,
      top_earlgrey,
    ],
  ),
)
sw_tests += {
  'hmac_enc_test': {
    'library': hmac_enc_test_lib,
  }
}

# SPI_HOST test
spi_host_smoketest_lib = declare_dependency(
  link_with: static_library(
    'spi_host_smoketest_lib',
    sources: ['spi_host_smoketest.c'],
    dependencies: [
      sw_lib_dif_spi_host,
      sw_lib_mmio,
      sw_lib_runtime_hart,
      top_earlgrey,
    ],
  ),
)
sw_tests += {
  'spi_host_smoketest': {
    'library': spi_host_smoketest_lib,
  }
}

###############################################################################
# Auto-generated tests
###############################################################################
subdir('autogen')

###############################################################################
# DV Simulation (target-specific) Tests
###############################################################################
subdir('sim_dv')

###############################################################################
# Closed Source Test Libraries
###############################################################################
if (get_option('closed_source_dir') != '')
  subdir('closed_source')
endif

###############################################################################
# Other Tests
###############################################################################
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

crt_test_lib = declare_dependency(
  link_with: static_library(
    'crt_test_lib',
    sources: ['crt_test.c'],
    dependencies: [
      sw_lib_testing_test_status,
      sw_lib_runtime_print,
      sw_lib_runtime_log,
      sw_lib_dif_uart,
    ],
  ),
)
sw_tests += {
  'crt_test': {
    'library': crt_test_lib,
    'ottf_start_only': true,
  }
}

###############################################################################
# Build Targets
###############################################################################
foreach sw_test_name, sw_test_info : sw_tests
  foreach device_name, device_lib : sw_lib_arch_core_devices
    targets_to_export = []
    shared_test_deps = [device_lib]

    if 'run_at_rom_stage' in sw_test_info and sw_test_info['run_at_rom_stage']

      # Build the test ELF for ROM.
      sw_test_elf = executable(
        sw_test_name + '_' + device_name,
        name_suffix: 'elf',
        link_args: test_rom_link_args,
        link_depends: test_rom_link_deps,
        sources: [
          hw_ip_ast_reg_h,
          hw_ip_clkmgr_reg_h,
          hw_ip_csrng_reg_h,
          hw_ip_edn_reg_h,
          hw_ip_entropy_src_reg_h,
          hw_ip_otp_ctrl_reg_h,
          hw_ip_sram_ctrl_reg_h,
          hw_ip_sensor_ctrl_reg_h,
          meson.project_source_root() / 'sw/device/lib/testing/test_rom/test_rom_start.S',
          meson.project_source_root() / 'sw/device/lib/testing/test_rom/test_rom.c',
          meson.project_source_root() / 'sw/device/lib/testing/test_rom/bootstrap.c',
        ],
        dependencies: [
          chip_info_h,
          sw_lib_crt,
          sw_lib_runtime_hart,
          sw_lib_runtime_print,
          sw_lib_flash_ctrl,
          sw_lib_ibex,
          sw_lib_pinmux,
          sw_lib_dif_gpio,
          sw_lib_dif_spi_device,
          sw_lib_dif_hmac,
          sw_lib_mmio,
          sw_lib_runtime_log,
          sw_lib_dif_uart,
          top_earlgrey,
          device_lib,
          sw_lib_testing_test_status,
          shared_test_deps,
          sw_lib_crt,
          sw_test_info['library'],
        ],
      )
    else
      if 'ottf_start_only' in sw_test_info and sw_test_info['ottf_start_only']
        # Explicitly ONLY pull in the OTTF startup library since these tests need
        # to run right after ottf_start.S is done executing. Additionally, the
        # startup library contains default OTTF ISRs. While these tests may not
        # override any of the default ISR symbols, they should be linked in since
        # the `mtvec` is set to point to these in the `ottf_start.S`
        # initialization assembly (contained in the ottf_start_lib target below).
        shared_test_deps += [
          ottf_start_lib,
        ]
      else
        shared_test_deps += [
          ottf_lib,
        ]
      endif

      # Build the test ELF for flash.
      if (get_option('closed_source_dir') != '') and \
        'link_with_closed_configs' in sw_test_info and \
        sw_test_info['link_with_closed_configs']
        sw_test_elf = executable(
          sw_test_name + '_' + device_name,
          name_suffix: 'elf',
          # Need to force the linker to examine (strong) symbols that may have a
          # weak implementation in the (static) test library.
          link_whole: closed_source_config_hooks_lib,
          dependencies: [
            shared_test_deps,
            sw_test_info['library'],
            closed_source_config_hooks_dep,
          ],
        )
      else
        sw_test_elf = executable(
          sw_test_name + '_' + device_name,
          name_suffix: 'elf',
          dependencies: [
            shared_test_deps,
            sw_test_info['library'],
          ],
        )
      endif
    endif

    target_name = sw_test_name + '_@0@_' + device_name

    sw_test_dis = custom_target(
      target_name.format('dis'),
      input: sw_test_elf,
      kwargs: elf_to_dis_custom_target_args,
    )

    sw_test_bin = custom_target(
      target_name.format('bin'),
      input: sw_test_elf,
      kwargs: elf_to_bin_custom_target_args,
    )

    targets_to_export += [
      sw_test_elf,
      sw_test_dis,
      sw_test_bin,
    ]

    if 'run_at_rom_stage' in sw_test_info and sw_test_info['run_at_rom_stage']
      # Test image is destined for ROM.
      sw_test_scr_vmem32 = custom_target(
        target_name.format('scr_vmem32'),
        command: scramble_image_command,
        depend_files: scramble_image_depend_files,
        input: sw_test_elf,
        output: scramble_image_outputs,
        build_by_default: true,
      )

      targets_to_export += [
        sw_test_scr_vmem32,
      ]
    else
      # Unsigned test image destined for flash, loaded with the test ROM.
      sw_test_vmem64 = custom_target(
        target_name.format('vmem64'),
        input: sw_test_bin,
        kwargs: bin_to_vmem64_custom_target_args,
      )

      sw_test_scr_vmem64 = custom_target(
        target_name.format('scr_vmem64'),
        input: sw_test_vmem64,
        output: flash_image_outputs,
        command: flash_image_command,
        depend_files: flash_image_depend_files,
        build_by_default: true,
      )

      targets_to_export += [
        sw_test_vmem64,
        sw_test_scr_vmem64,
      ]

      # Signed test image destined for flash, loaded with the mask ROM.
      if 'sign' in sw_test_info and sw_test_info['sign']
        foreach key_name, key_info : signing_keys
          signed_target_name = '_'.join([
            'signed',
            sw_test_name,
            key_name,
            '@0@',
            device_name,
          ])

          sw_test_signed_bin = custom_target(
            signed_target_name.format('bin'),
            input: sw_test_bin,
            output: '@BASENAME@.@0@.signed.bin'.format(key_name),
            command: [
              rom_ext_signer_export.full_path(),
              'rom_ext',
              '@INPUT@',
              key_info['path'],
              sw_test_elf.full_path(),
              '@OUTPUT@',
            ],
            depends: rom_ext_signer_export,
            build_by_default: true,
          )

          sw_test_signed_vmem64 = custom_target(
            signed_target_name.format('vmem64'),
            input: sw_test_signed_bin,
            kwargs: bin_to_vmem64_custom_target_args,
          )

          sw_test_signed_scr_vmem64 = custom_target(
            signed_target_name.format('scrambled'),
            input: sw_test_signed_vmem64,
            output: flash_image_outputs,
            command: flash_image_command,
            depend_files: flash_image_depend_files,
            build_by_default: true,
          )

          targets_to_export += [
            sw_test_signed_bin,
            sw_test_signed_vmem64,
            sw_test_signed_scr_vmem64,
          ]
        endforeach
      endif

      # DV sim bootstrap image (for loading flash images via bootstrap).
      if device_name == 'sim_dv' and \
          sw_test_info.has_key('dv_frames') and sw_test_info['dv_frames']
        sw_test_sim_dv_frames_bin = custom_target(
          sw_test_name + '_sim_dv_frames_bin',
          command: [
            spiflash_bin,
            '--input=@INPUT@',
            '--dump-frames=@OUTPUT@',
          ],
          input: sw_test_bin,
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

        targets_to_export += [
          sw_test_sim_dv_frames_bin,
          sw_test_sim_dv_frames_vmem,
        ]
      endif
    endif

    if device_name == 'sim_dv'
      sw_test_sim_dv_logs = custom_target(
        sw_test_name + '_sim_dv_logs',
        command: extract_sw_logs_sim_dv_command,
        depend_files: [extract_sw_logs_sim_dv_depend_files,],
        input: sw_test_elf,
        output: extract_sw_logs_sim_dv_outputs,
      )

      targets_to_export += [sw_test_sim_dv_logs]
    endif

    custom_target(
      target_name.format('export'),
      command: export_target_command,
      depend_files: [export_target_depend_files,],
      input: targets_to_export,
      output: target_name.format('export'),
      build_always_stale: true,
      build_by_default: true,
    )
  endforeach
endforeach
