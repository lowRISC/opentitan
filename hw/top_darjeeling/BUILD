# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules/opentitan:defs.bzl",
    "DEFAULT_TEST_FAILURE_MSG",
    "DEFAULT_TEST_SUCCESS_MSG",
    "sim_dv",
)

package(default_visibility = ["//visibility:public"])

###########################################################################
# Sim DV Environments
#
# The sim_dv_base target is only meant to be used for building ROMs and
# other items without `testonly=True`.
###########################################################################

# Remark: we must use a different name from earlgrey because the test point
# names are derived from the exec_env's target named
sim_dv(
    name = "sim_dv_base",
    design = "darjeeling",
    exec_env = "sim_dv",
    extract_sw_logs = "//util/device_sw_utils:extract_sw_logs_db",
    flash_scramble_tool = "//util/design:gen-flash-img",
    libs = [
        "//sw/device/lib/arch:boot_stage_rom_ext",
        "//sw/device/lib/arch:sim_dv",
    ],
    linker_script = "//sw/device/lib/testing/test_framework:ottf_ld_silicon_creator_slot_a",
    rom_scramble_config = "//hw/top_darjeeling/data/autogen:top_darjeeling.gen.hjson",
)

sim_dv(
    name = "sim_dv",
    testonly = True,
    base = ":sim_dv_base",
    exec_env = "sim_dv",
    rom = "//sw/device/lib/testing/test_rom:test_rom",
)

# Initial list of DV sims required by Robert, extracted
# from the DV testplan.
test_suite(
    name = "initial_test_list",
    tests = [
        "//sw/device/tests:otbn_randomness_test_sim_dv",
        "//sw/device/tests:pwrmgr_random_sleep_all_reset_reqs_test_sim_dv",
        "//sw/device/tests:rstmgr_alert_info_test_sim_dv",
        "//sw/device/tests:rstmgr_cpu_info_test_sim_dv",
        "//sw/device/tests:rstmgr_sw_req_test_sim_dv",
        "//sw/device/tests:rstmgr_sw_rst_ctrl_test_sim_dv",
        "//sw/device/tests:rv_core_ibex_nmi_irq_test_sim_dv",
        "//sw/device/tests:rv_core_ibex_rnd_test_sim_dv",
        "//sw/device/tests/sim_dv:alert_handler_lpg_sleep_mode_alerts_test_sim_dv",
    ],
)

test_suite(
    name = "initial_test_list2",
    tests = [
        # base_rom_e2e_smoke?
        "//sw/device/tests/autogen:plic_all_irqs_test_0_sim_dv",
        "//sw/device/tests/autogen:plic_all_irqs_test_1_sim_dv",
        "//sw/device/tests/autogen:plic_all_irqs_test_2_sim_dv",
        # "//sw/device/tests:rv_dm_lc_disabled_tl_sim_dv",
        # "//sw/device/tests:rv_dm_lc_disabled_jtag_sim_dv",
        "//sw/device/tests:kmac_app_rom_test_sim_dv",
        "//sw/device/tests:rstmgr_sw_rst_ctrl_test_sim_dv",
        "//sw/device/tests:hmac_enc_test_sim_dv",
        "//sw/device/tests:clkmgr_jitter_test_sim_dv",
        "//sw/device/tests/sim_dv:rom_ctrl_integrity_check_test_sim_dv",
        "//sw/device/tests:aes_entropy_test_sim_dv",
        "//sw/device/tests:kmac_idle_test_sim_dv",
        "//sw/device/tests:kmac_mode_cshake_test_sim_dv",
        "//sw/device/tests:kmac_mode_kmac_test_sim_dv",
        "//sw/device/tests/sim_dv:lc_ctrl_scrap_test_sim_dv",
        "//sw/device/tests:sleep_pin_mio_dio_val_test_sim_dv",
    ],
)

test_suite(
    name = "initial_test_list3",
    tests = [
        "//sw/device/tests:power_virus_systemtest_sim_dv",
    ],
)
