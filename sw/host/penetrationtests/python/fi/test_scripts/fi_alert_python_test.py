# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from sw.host.penetrationtests.python.fi.host_scripts import fi_alert_functions
from sw.host.penetrationtests.python.fi.communication.fi_alert_commands import OTFIAlert
from python.runfiles import Runfiles
from sw.host.penetrationtests.python.util import targets
from sw.host.penetrationtests.python.util import utils
from sw.host.penetrationtests.python.util import common_library
import json
import unittest
import argparse
import sys

ignored_keys_set = set([])
opentitantool_path = ""

target = None
is_fpga = False

# Read in the extra arguments from the opentitan_test.
parser = argparse.ArgumentParser()
parser.add_argument("--bitstream", type=str)
parser.add_argument("--bootstrap", type=str)

args, config_args = parser.parse_known_args()

BITSTREAM = args.bitstream
BOOTSTRAP = args.bootstrap

case_to_alert_list_map = [
    42,  # Case 0 maps to alert_list index 42 ("aes_recov_ctrl_update_err")
    43,  # Case 1 maps to alert_list index 43 ("aes_fatal_fault")
    31,  # Case 2 maps to alert_list index 31 ("aon_timer_aon_fatal_fault")
    25,  # Case 3 maps to alert_list index 25 ("clkmgr_aon_recov_fault")
    26,  # Case 4 maps to alert_list index 26 ("clkmgr_aon_fatal_fault")
    51,  # Case 5 maps to alert_list index 51 ("csrng_recov_alert")
    52,  # Case 6 maps to alert_list index 52 ("csrng_fatal_alert")
    55,  # Case 7 maps to alert_list index 55 ("edn0_recov_alert")
    56,  # Case 8 maps to alert_list index 56 ("edn0_fatal_alert")
    57,  # Case 9 maps to alert_list index 57 ("edn1_recov_alert")
    58,  # Case 10 maps to alert_list index 58 ("edn1_fatal_alert")
    53,  # Case 11 maps to alert_list index 53 ("entropy_src_recov_alert")
    54,  # Case 12 maps to alert_list index 54 ("entropy_src_fatal_alert")
    35,  # Case 13 maps to alert_list index 35 ("flash_ctrl_recov_err")
    36,  # Case 14 maps to alert_list index 36 ("flash_ctrl_fatal_std_err")
    37,  # Case 15 maps to alert_list index 37 ("flash_ctrl_fatal_err")
    38,  # Case 16 maps to alert_list index 38 ("flash_ctrl_fatal_prim_flash_alert")
    39,  # Case 17 maps to alert_list index 39 ("flash_ctrl_recov_prim_flash_alert")
    4,  # Case 18 maps to alert_list index 4 ("gpio_fatal_fault")
    44,  # Case 19 maps to alert_list index 44 ("hmac_fatal_fault")
    6,  # Case 20 maps to alert_list index 6 ("i2c0_fatal_fault")
    7,  # Case 21 maps to alert_list index 7 ("i2c1_fatal_fault")
    8,  # Case 22 maps to alert_list index 8 ("i2c2_fatal_fault")
    49,  # Case 23 maps to alert_list index 49 ("keymgr_recov_operation_err")
    50,  # Case 24 maps to alert_list index 50 ("keymgr_fatal_fault_err")
    45,  # Case 25 maps to alert_list index 45 ("kmac_recov_operation_err")
    46,  # Case 26 maps to alert_list index 46 ("kmac_fatal_fault_err")
    16,  # Case 27 maps to alert_list index 16 ("lc_ctrl_fatal_prog_error")
    17,  # Case 28 maps to alert_list index 17 ("lc_ctrl_fatal_state_error")
    18,  # Case 29 maps to alert_list index 18 ("lc_ctrl_fatal_bus_integ_error")
    47,  # Case 30 maps to alert_list index 47 ("otbn_fatal")
    48,  # Case 31 maps to alert_list index 48 ("otbn_recov")
    11,  # Case 32 maps to alert_list index 11 ("otp_ctrl_fatal_macro_error")
    12,  # Case 33 maps to alert_list index 12 ("otp_ctrl_fatal_check_error")
    13,  # Case 34 maps to alert_list index 13 ("otp_ctrl_fatal_bus_integ_error")
    14,  # Case 35 maps to alert_list index 14 ("otp_ctrl_fatal_prim_otp_alert")
    15,  # Case 36 maps to alert_list index 15 ("otp_ctrl_recov_prim_otp_alert")
    9,  # Case 37 maps to alert_list index 9 ("pattgen_fatal_fault")
    30,  # Case 38 maps to alert_list index 30 ("pinmux_aon_fatal_fault")
    29,  # Case 39 maps to alert_list index 29 ("pwm_aon_fatal_fault")
    22,  # Case 40 maps to alert_list index 22 ("pwrmgr_aon_fatal_fault")
    60,  # Case 41 maps to alert_list index 60 ("rom_ctrl_fatal")
    23,  # Case 42 maps to alert_list index 23 ("rstmgr_aon_fatal_fault")
    24,  # Case 43 maps to alert_list index 24 ("rstmgr_aon_fatal_cnsty_fault")
    61,  # Case 44 maps to alert_list index 61 ("rv_core_ibex_fatal_sw_err")
    62,  # Case 45 maps to alert_list index 62 ("rv_core_ibex_recov_sw_err")
    63,  # Case 46 maps to alert_list index 63 ("rv_core_ibex_fatal_hw_err")
    64,  # Case 47 maps to alert_list index 64 ("rv_core_ibex_recov_hw_err")
    41,  # Case 48 maps to alert_list index 41 ("rv_plic_fatal_fault")
    10,  # Case 49 maps to alert_list index 10 ("rv_timer_fatal_fault")
    32,  # Case 50 maps to alert_list index 32 ("sensor_ctrl_recov_alert")
    33,  # Case 51 maps to alert_list index 33 ("sensor_ctrl_fatal_alert")
    5,  # Case 52 maps to alert_list index 5 ("spi_device_fatal_fault")
    19,  # Case 53 maps to alert_list index 19 ("spi_host0_fatal_fault")
    20,  # Case 54 maps to alert_list index 20 ("spi_host1_fatal_fault")
    59,  # Case 55 maps to alert_list index 59 ("sram_ctrl_main_fatal_error")
    34,  # Case 56 maps to alert_list index 34 ("sram_ctrl_ret_aon_fatal_error")
    27,  # Case 57 maps to alert_list index 27 ("sysrst_ctrl_aon_fatal_fault")
    0,  # Case 58 maps to alert_list index 0 ("uart0_fatal_fault")
    1,  # Case 59 maps to alert_list index 1 ("uart1_fatal_fault")
    2,  # Case 60 maps to alert_list index 2 ("uart2_fatal_fault")
    3,  # Case 61 maps to alert_list index 3 ("uart3_fatal_fault")
    21,  # Case 62 maps to alert_list index 21 ("usbdev_fatal_fault")
]


class AlertFiTest(unittest.TestCase):
    def test_init(self):
        alertfi = OTFIAlert(target)
        device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = alertfi.init(
            alert_config=common_library.default_fpga_friendly_alert_config
        )
        device_id_json = json.loads(device_id)
        sensors_json = json.loads(sensors)
        alerts_json = json.loads(alerts)
        owner_page_json = json.loads(owner_page)
        boot_log_json = json.loads(boot_log)
        boot_measurements_json = json.loads(boot_measurements)

        expected_device_id_keys = {
            "device_id",
            "rom_digest",
            "icache_en",
            "dummy_instr_en",
            "clock_jitter_locked",
            "clock_jitter_en",
            "sram_main_readback_locked",
            "sram_main_readback_en",
            "sram_ret_readback_locked",
            "sram_ret_readback_en",
            "data_ind_timing_en",
        }
        actual_device_id_keys = set(device_id_json.keys())

        self.assertEqual(
            expected_device_id_keys,
            actual_device_id_keys,
            "device_id keys do not match",
        )

        expected_sensors_keys = {"sensor_ctrl_en", "sensor_ctrl_fatal"}
        actual_sensors_keys = set(sensors_json.keys())

        self.assertEqual(expected_sensors_keys, actual_sensors_keys, "sensor keys do not match")

        expected_alerts_keys = {
            "alert_classes",
            "loc_alert_classes",
            "enabled_alerts",
            "enabled_loc_alerts",
            "enabled_classes",
            "accumulation_thresholds",
            "duration_cycles",
            "escalation_signals_en",
            "escalation_signals_map",
        }
        actual_alerts_keys = set(alerts_json.keys())

        self.assertEqual(expected_alerts_keys, actual_alerts_keys, "alert keys do not match")

        expected_owner_page_keys = {
            "config_version",
            "sram_exec_mode",
            "ownership_key_alg",
            "update_mode",
            "min_security_version_bl0",
            "lock_constraint",
        }
        actual_owner_page_keys = set(owner_page_json.keys())

        self.assertEqual(
            expected_owner_page_keys,
            actual_owner_page_keys,
            "owner_page keys do not match",
        )

        expected_boot_log_keys = {
            "digest",
            "identifier",
            "scm_revision_low",
            "scm_revision_high",
            "rom_ext_slot",
            "rom_ext_major",
            "rom_ext_minor",
            "rom_ext_size",
            "bl0_slot",
            "ownership_state",
            "ownership_transfers",
            "rom_ext_min_sec_ver",
            "bl0_min_sec_ver",
            "primary_bl0_slot",
            "retention_ram_initialized",
        }
        actual_boot_log_keys = set(boot_log_json.keys())

        self.assertEqual(expected_boot_log_keys, actual_boot_log_keys, "boot_log keys do not match")

        expected_boot_measurements_keys = {"bl0", "rom_ext"}
        actual_boot_measurements_keys = set(boot_measurements_json.keys())

        self.assertEqual(
            expected_boot_measurements_keys,
            actual_boot_measurements_keys,
            "boot_measurements keys do not match",
        )

        self.assertIn("PENTEST", version)

    # We check the default alert config by writing to the alert_test registers
    def test_char_alert_trigger(self):
        # The exception list spans spi and usb alerts since those blocks will
        # no longer function after a recoverable alert
        exception_list = [19, 20, 21]
        # On the FPGA, we exclude flash_ctrl_fatal_err
        if is_fpga:
            exception_list.extend([37])
        print(exception_list)
        for alert in range(63):
            translated_alert = case_to_alert_list_map[alert]
            if translated_alert not in exception_list:
                actual_result, got_response = fi_alert_functions.char_alert_trigger(
                    target, alert, reset=True
                )
                alert_class = common_library.default_fpga_friendly_alert_config["alert_classes"][
                    translated_alert
                ]
                alert_enabled = common_library.default_fpga_friendly_alert_config["enable_alerts"][
                    translated_alert
                ]
                enabled_class = common_library.default_fpga_friendly_alert_config["enable_classes"][
                    alert_class
                ]
                threshold = common_library.default_fpga_friendly_alert_config[
                    "accumulation_thresholds"
                ][alert_class]
                reset_enabled = 3 in common_library.default_fpga_friendly_alert_config["signals"]

                if reset_enabled and alert_enabled and enabled_class and (threshold == 0):
                    self.assertEqual(
                        got_response,
                        False,
                        msg=f"Expected a reset but got an output. \
                                        Failed for input {alert} and response {actual_result}",
                    )
                else:
                    self.assertEqual(
                        got_response,
                        True,
                        msg=f"Expected an output but got a reset. \
                                        Failed for input {alert}",
                    )
                    actual_result_json = json.loads(actual_result)
                    alert_array = [0, 0, 0]
                    if translated_alert < 32:
                        alert_array[0] = 1 << translated_alert
                    elif translated_alert < 64:
                        alert_array[1] = 1 << (translated_alert - 32)
                    else:
                        alert_array[2] = 1 << (translated_alert - 64)
                    expected_result_json = {
                        "err_status": 0,
                        "alerts": alert_array,
                        "loc_alerts": 0,
                        "ast_alerts": [0, 0],
                    }
                    utils.compare_json_data(
                        actual_result_json, expected_result_json, ignored_keys_set
                    )

    # We check the default alert config by writing to the alert_trig register in the sensor control
    def test_char_alert_sensor_ctrl_trigger(self):
        actual_result, got_response = fi_alert_functions.char_alert_sensor_ctrl_trigger(
            target, reset=True
        )
        sensor_cntr_recov = case_to_alert_list_map[50]
        sensor_cntr_fatal = case_to_alert_list_map[51]
        alert_recov_enabled = common_library.default_fpga_friendly_alert_config["enable_alerts"][
            sensor_cntr_recov
        ]
        alert_fatal_enabled = common_library.default_fpga_friendly_alert_config["enable_alerts"][
            sensor_cntr_fatal
        ]
        sensor_ctrl_en_fatal = common_library.default_sensor_config["sensor_ctrl_en_fatal"][0]
        reset_enabled = 3 in common_library.default_fpga_friendly_alert_config["signals"]

        if reset_enabled and (
            (sensor_ctrl_en_fatal and alert_fatal_enabled)
            or (not sensor_ctrl_en_fatal and alert_recov_enabled)
        ):
            self.assertEqual(
                got_response,
                False,
                msg="Expected a reset but got an output for the alert_trig.",
            )
        else:
            self.assertEqual(
                got_response,
                True,
                msg="Expected an output but got a reset for the alert_trig",
            )

    # We check the default alert config by writing to the fatal sw alert from ibex
    def test_char_alert_ibex_sw_fatal(self):
        actual_result, got_response = fi_alert_functions.char_alert_ibex_sw_fatal(
            target, reset=True
        )
        ibex_sw_fatal = case_to_alert_list_map[44]
        alert_class = common_library.default_fpga_friendly_alert_config["alert_classes"][
            ibex_sw_fatal
        ]
        alert_fatal_enabled = common_library.default_fpga_friendly_alert_config["enable_alerts"][
            ibex_sw_fatal
        ]
        reset_enabled = 3 in common_library.default_fpga_friendly_alert_config["signals"]
        enabled_class = common_library.default_fpga_friendly_alert_config["enable_classes"][
            alert_class
        ]

        if reset_enabled and alert_fatal_enabled and enabled_class:
            self.assertEqual(
                got_response,
                False,
                msg="Expected a reset but got an output for the ibex sw fatal.",
            )
        elif alert_fatal_enabled:
            self.assertEqual(
                got_response,
                True,
                msg="Expected an output but got a reset for the ibex sw fatal",
            )
            actual_result_json = json.loads(actual_result)
            alert_array = [0, 0, 0]
            if ibex_sw_fatal < 32:
                alert_array[0] = 1 << ibex_sw_fatal
            elif ibex_sw_fatal < 64:
                alert_array[1] = 1 << (ibex_sw_fatal - 32)
            else:
                alert_array[2] = 1 << (ibex_sw_fatal - 64)
            expected_result_json = {
                "err_status": 0,
                "alerts": alert_array,
                "loc_alerts": 0,
                "ast_alerts": [0, 0],
            }
            utils.compare_json_data(actual_result_json, expected_result_json, ignored_keys_set)
        else:
            self.assertEqual(
                got_response,
                True,
                msg="Expected an output but got a reset for the aes ctrl",
            )
            actual_result_json = json.loads(actual_result)
            expected_result_json = {
                "err_status": 0,
                "alerts": [0, 0, 0],
                "loc_alerts": 0,
                "ast_alerts": [0, 0],
            }
            utils.compare_json_data(actual_result_json, expected_result_json, ignored_keys_set)


if __name__ == "__main__":
    r = Runfiles.Create()
    # Get the opentitantool path.
    opentitantool_path = r.Rlocation("lowrisc_opentitan/sw/host/opentitantool/opentitantool")
    # Program the bitstream for FPGAs.
    bitstream_path = None
    if BITSTREAM:
        bitstream_path = r.Rlocation("lowrisc_opentitan/" + BITSTREAM)
    # Get the firmware path.
    firmware_path = r.Rlocation("lowrisc_opentitan/" + BOOTSTRAP)

    if "fpga" in BOOTSTRAP:
        target_type = "fpga"
        is_fpga = True
    else:
        target_type = "chip"

    target_cfg = targets.TargetConfig(
        target_type=target_type,
        interface_type="hyperdebug",
        fw_bin=firmware_path,
        opentitantool=opentitantool_path,
        bitstream=bitstream_path,
        tool_args=config_args,
    )

    target = targets.Target(target_cfg)

    target.initialize_target()

    unittest.main(argv=[sys.argv[0]])
