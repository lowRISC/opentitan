# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

dif_rv_plic_smoketest_lib = declare_dependency(
  link_with: static_library(
    'dif_rv_plic_smoketest_lib',
    sources: ['dif_rv_plic_smoketest.c'],
    dependencies: [
      sw_lib_dif_uart,
      sw_lib_dif_rv_plic,
      sw_lib_irq,
      sw_lib_mmio,
      sw_lib_runtime_log,
      sw_lib_runtime_hart,
      sw_lib_testing_test_status,
    ],
  ),
)
sw_tests += {
  'dif_rv_plic_smoketest': {
    'library': dif_rv_plic_smoketest_lib,
  }
}

dif_uart_smoketest_lib = declare_dependency(
  link_with: static_library(
    'dif_uart_smoketest_lib',
    sources: ['dif_uart_smoketest.c'],
    dependencies: [
      sw_lib_dif_uart,
      sw_lib_mmio,
      sw_lib_runtime_hart,
    ],
  ),
)
sw_tests += {
  'dif_uart_smoketest': {
    'library': dif_uart_smoketest_lib,
  }
}
sw_rom_ext_tests += {
  'dif_uart_smoketest': {
    'library': dif_uart_smoketest_lib,
  }
}

dif_rv_timer_smoketest_lib = declare_dependency(
  link_with: static_library(
    'dif_rv_timer_smoketest_lib',
    sources: ['dif_rv_timer_smoketest.c'],
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
  'dif_rv_timer_smoketest': {
    'library': dif_rv_timer_smoketest_lib,
  }
}

dif_hmac_smoketest_lib = declare_dependency(
  link_with: static_library(
    'dif_hmac_smoketest_lib',
    sources: ['dif_hmac_smoketest.c'],
    dependencies: [
      sw_lib_dif_hmac,
      sw_lib_runtime_log,
      sw_lib_mmio,
      sw_lib_runtime_hart,
    ],
  ),
)
sw_tests += {
  'dif_hmac_smoketest': {
    'library': dif_hmac_smoketest_lib,
  }
}

dif_kmac_smoketest_lib = declare_dependency(
  link_with: static_library(
    'dif_kmac_smoketest_lib',
    sources: ['dif_kmac_smoketest.c'],
    dependencies: [
      sw_lib_dif_kmac,
      sw_lib_runtime_log,
      sw_lib_mmio,
      sw_lib_runtime_hart,
    ],
  ),
)
sw_tests += {
  'dif_kmac_smoketest': {
    'library': dif_kmac_smoketest_lib,
  }
}

dif_kmac_cshake_smoketest_lib = declare_dependency(
  link_with: static_library(
    'dif_kmac_cshake_smoketest_lib',
    sources: ['dif_kmac_cshake_smoketest.c'],
    dependencies: [
      sw_lib_dif_kmac,
      sw_lib_runtime_log,
      sw_lib_mmio,
      sw_lib_runtime_hart,
    ],
  ),
)
sw_tests += {
  'dif_kmac_cshake_smoketest': {
    'library': dif_kmac_cshake_smoketest_lib,
  }
}

dif_kmac_kmac_smoketest_lib = declare_dependency(
  link_with: static_library(
    'dif_kmac_kmac_smoketest_lib',
    sources: ['dif_kmac_kmac_smoketest.c'],
    dependencies: [
      sw_lib_dif_kmac,
      sw_lib_runtime_log,
      sw_lib_mmio,
      sw_lib_runtime_hart,
    ],
  ),
)
sw_tests += {
  'dif_kmac_kmac_smoketest': {
    'library': dif_kmac_kmac_smoketest_lib,
  }
}

dif_rstmgr_smoketest_lib = declare_dependency(
  link_with: static_library(
    'dif_rstmgr_smoketest_lib',
    sources: ['dif_rstmgr_smoketest.c'],
    dependencies: [
      sw_lib_dif_rstmgr,
      sw_lib_mmio,
      sw_lib_runtime_hart,
    ],
  ),
)
sw_tests += {
  'dif_rstmgr_smoketest': {
    'library': dif_rstmgr_smoketest_lib,
  }
}

dif_otbn_smoketest_lib = declare_dependency(
  link_with: static_library(
    'dif_otbn_smoketest_lib',
    sources: ['dif_otbn_smoketest.c'],
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
  'dif_otbn_smoketest': {
    'library': dif_otbn_smoketest_lib,
  }
}

dif_otp_ctrl_smoketest_lib = declare_dependency(
  link_with: static_library(
    'dif_otp_ctrl_smoketest_lib',
    sources: ['dif_otp_ctrl_smoketest.c'],
    dependencies: [
      sw_lib_dif_otp_ctrl,
      sw_lib_runtime_log,
      sw_lib_mmio,
      sw_lib_runtime_hart,
    ],
  ),
)
sw_tests += {
  'dif_otp_ctrl_smoketest': {
    'library': dif_otp_ctrl_smoketest_lib,
  }
}

dif_gpio_smoketest_lib = declare_dependency(
  link_with: static_library(
    'dif_gpio_smoketest_lib',
    sources: ['dif_gpio_smoketest.c'],
    dependencies: [
      sw_lib_dif_gpio,
      sw_lib_mmio,
      sw_lib_runtime_log,
    ],
  ),
)
sw_tests += {
  'dif_gpio_smoketest': {
    'library': dif_gpio_smoketest_lib,
  }
}

dif_aes_smoketest_lib = declare_dependency(
  link_with: static_library(
    'dif_aes_smoketest_lib',
    sources: ['dif_aes_smoketest.c'],
    dependencies: [
      sw_lib_dif_aes,
      sw_lib_mmio,
      sw_lib_runtime_log,
      sw_lib_testing_entropy_testutils,
      sw_lib_testing_test_status,
    ],
  ),
)
sw_tests += {
  'dif_aes_smoketest': {
    'library': dif_aes_smoketest_lib,
  }
}

dif_clkmgr_smoketest_lib = declare_dependency(
  link_with: static_library(
    'dif_clkmgr_smoketest_lib',
    sources: ['dif_clkmgr_smoketest.c'],
    dependencies: [
      sw_lib_dif_clkmgr,
      sw_lib_mmio,
      sw_lib_runtime_log,
    ],
  ),
)
sw_tests += {
  'dif_clkmgr_smoketest': {
    'library': dif_clkmgr_smoketest_lib,
  }
}

dif_csrng_smoketest_lib = declare_dependency(
  link_with: static_library(
    'dif_csrng_smoketest_lib',
    sources: ['dif_csrng_smoketest.c'],
    dependencies: [
      sw_lib_dif_csrng,
      sw_lib_mmio,
      sw_lib_runtime_log,
    ],
  ),
)
sw_tests += {
  'dif_csrng_smoketest': {
    'library': dif_csrng_smoketest_lib,
  }
}

dif_entropy_src_smoketest_lib = declare_dependency(
  link_with: static_library(
    'dif_entropy_src_smoketest_lib',
    sources: ['dif_entropy_src_smoketest.c'],
    dependencies: [
      sw_lib_dif_entropy_src,
      sw_lib_mmio,
      sw_lib_runtime_log,
    ],
  ),
)
sw_tests += {
  'dif_entropy_src_smoketest': {
    'library': dif_entropy_src_smoketest_lib,
  }
}

dif_aon_timer_smoketest_lib = declare_dependency(
  link_with: static_library(
    'dif_aon_timer_smoketest_lib',
    sources: ['dif_aon_timer_smoketest.c'],
    dependencies: [
      sw_lib_dif_aon_timer,
      sw_lib_mmio,
      sw_lib_runtime_log,
    ],
  ),
)
sw_tests += {
  'dif_aon_timer_smoketest': {
    'library': dif_aon_timer_smoketest_lib,
  }
}

dif_pwrmgr_smoketest_lib = declare_dependency(
  link_with: static_library(
    'dif_pwrmgr_smoketest_lib',
    sources: ['dif_pwrmgr_smoketest.c'],
    dependencies: [
      sw_lib_dif_pwrmgr,
      sw_lib_dif_aon_timer,
      sw_lib_mmio,
      sw_lib_runtime_log,
    ],
  ),
)
sw_tests += {
  'dif_pwrmgr_smoketest': {
    'library': dif_pwrmgr_smoketest_lib,
  }
}
