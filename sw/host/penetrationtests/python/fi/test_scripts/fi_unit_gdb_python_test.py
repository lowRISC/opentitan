# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from sw.host.penetrationtests.python.fi.communication.fi_unit_gdb_commands import OTFIUnitGdb
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

# Read in the extra arguments from the opentitan_test.
parser = argparse.ArgumentParser()
parser.add_argument("--bitstream", type=str)
parser.add_argument("--bootstrap", type=str)

args, config_args = parser.parse_known_args()

BITSTREAM = args.bitstream
BOOTSTRAP = args.bootstrap


class UnitGdbTest(unittest.TestCase):
    def test_init(self):
        gdbfi = OTFIUnitGdb(target)
        device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = gdbfi.init(
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

    def test_char_gdb_try(self):
        gdbfi = OTFIUnitGdb(target)
        device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = gdbfi.init(
            alert_config=common_library.default_fpga_friendly_alert_config
        )
        gdbfi.handle_gdb_try()
        actual_result = target.read_response()
        actual_result_json = json.loads(actual_result)
        expected_result_json = json.loads(
            '{"result":true, \
                "status":0, \
                "err_status":0, \
                "alerts":[0,0,0], \
                "loc_alerts":0, \
                "ast_alerts":[0,0] \
            }'
        )
        utils.compare_json_data(actual_result_json, expected_result_json, ignored_keys_set)

    def test_char_gdb_switch(self):
        gdbfi = OTFIUnitGdb(target)
        device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = gdbfi.init(
            alert_config=common_library.default_fpga_friendly_alert_config
        )
        gdbfi.handle_gdb_switch()
        actual_result = target.read_response()
        actual_result_json = json.loads(actual_result)
        expected_result_json = json.loads(
            '{"result":true, \
                "status":0, \
                "err_status":0, \
                "alerts":[0,0,0], \
                "loc_alerts":0, \
                "ast_alerts":[0,0] \
            }'
        )
        utils.compare_json_data(actual_result_json, expected_result_json, ignored_keys_set)

    def test_char_gdb_if(self):
        gdbfi = OTFIUnitGdb(target)
        device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = gdbfi.init(
            alert_config=common_library.default_fpga_friendly_alert_config
        )
        gdbfi.handle_gdb_if()
        actual_result = target.read_response()
        actual_result_json = json.loads(actual_result)
        expected_result_json = json.loads(
            '{"result":true, \
                "status":0, \
                "err_status":0, \
                "alerts":[0,0,0], \
                "loc_alerts":0, \
                "ast_alerts":[0,0] \
            }'
        )
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
