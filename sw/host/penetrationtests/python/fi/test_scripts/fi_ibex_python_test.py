# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from sw.host.penetrationtests.python.fi.host_scripts import fi_ibex_functions
from sw.host.penetrationtests.python.fi.communication.fi_ibex_commands import OTFIIbex
from python.runfiles import Runfiles
from sw.host.penetrationtests.python.util import targets
from sw.host.penetrationtests.python.util import utils
from sw.host.penetrationtests.python.util import common_library
import json
import unittest
import argparse
import sys

opentitantool_path = ""
iterations = 3
ignored_keys_set = set(["registers", "registers_test_1", "registers_test_2", "registers_test_3"])

target = None

# Read in the extra arguments from the opentitan_test.
parser = argparse.ArgumentParser()
parser.add_argument("--bitstream", type=str)
parser.add_argument("--bootstrap", type=str)

args, config_args = parser.parse_known_args()

BITSTREAM = args.bitstream
BOOTSTRAP = args.bootstrap


def load_test_data(test_name):
    data_path = r.Rlocation(
        "lowrisc_opentitan/sw/host/penetrationtests/python/fi/gold_responses/fi_ibex.json"
    )

    with open(data_path, "r") as f:
        data = json.load(f)
        return data[test_name]


# Note that these tests influence CSRs and the Ibex in general, hence, we always reset between
# tests to ensure tests do not become flaky.
class IbexFiTest(unittest.TestCase):
    def test_init(self):
        ibexfi = OTFIIbex(target)
        device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = ibexfi.init(
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

    def test_char_addi_single_beq(self):
        actual_result = fi_ibex_functions.char_addi_single_beq(target, iterations)
        actual_result_json = json.loads(actual_result)
        expected_result_json = load_test_data("char_addi_single_beq")
        utils.compare_json_data(actual_result_json, expected_result_json, ignored_keys_set)

    def test_char_addi_single_beq_neg(self):
        actual_result = fi_ibex_functions.char_addi_single_beq_neg(target, iterations)
        actual_result_json = json.loads(actual_result)
        expected_result_json = load_test_data("char_addi_single_beq_neg")
        utils.compare_json_data(actual_result_json, expected_result_json, ignored_keys_set)

    def test_char_addi_single_bne(self):
        actual_result = fi_ibex_functions.char_addi_single_bne(target, iterations)
        actual_result_json = json.loads(actual_result)
        expected_result_json = load_test_data("char_addi_single_bne")
        utils.compare_json_data(actual_result_json, expected_result_json, ignored_keys_set)

    def test_char_addi_single_bne_neg(self):
        actual_result = fi_ibex_functions.char_addi_single_bne_neg(target, iterations)
        actual_result_json = json.loads(actual_result)
        expected_result_json = load_test_data("char_addi_single_bne_neg")
        utils.compare_json_data(actual_result_json, expected_result_json, ignored_keys_set)

    def test_char_combi(self):
        actual_result = fi_ibex_functions.char_combi(target, iterations)
        actual_result_json = json.loads(actual_result)
        expected_result_json = load_test_data("char_combi")
        utils.compare_json_data(actual_result_json, expected_result_json, ignored_keys_set)

    def test_char_conditional_branch_beq(self):
        actual_result = fi_ibex_functions.char_conditional_branch_beq(target, iterations)
        actual_result_json = json.loads(actual_result)
        expected_result_json = load_test_data("char_conditional_branch_beq")
        utils.compare_json_data(actual_result_json, expected_result_json, ignored_keys_set)

    def test_char_conditional_branch_bge(self):
        actual_result = fi_ibex_functions.char_conditional_branch_bge(target, iterations)
        actual_result_json = json.loads(actual_result)
        expected_result_json = load_test_data("char_conditional_branch_bge")
        utils.compare_json_data(actual_result_json, expected_result_json, ignored_keys_set)

    def test_char_conditional_branch_bgeu_test(self):
        actual_result = fi_ibex_functions.char_conditional_branch_bgeu(target, iterations)
        actual_result_json = json.loads(actual_result)
        expected_result_json = load_test_data("char_conditional_branch_bgeu")
        utils.compare_json_data(actual_result_json, expected_result_json, ignored_keys_set)

    def test_char_conditional_branch_blt(self):
        actual_result = fi_ibex_functions.char_conditional_branch_blt(target, iterations)
        actual_result_json = json.loads(actual_result)
        expected_result_json = load_test_data("char_conditional_branch_blt")
        utils.compare_json_data(actual_result_json, expected_result_json, ignored_keys_set)

    def test_char_conditional_branch_bltu(self):
        actual_result = fi_ibex_functions.char_conditional_branch_bltu(target, iterations)
        actual_result_json = json.loads(actual_result)
        expected_result_json = load_test_data("char_conditional_branch_bltu")
        utils.compare_json_data(actual_result_json, expected_result_json, ignored_keys_set)

    def test_char_conditional_branch_bne(self):
        actual_result = fi_ibex_functions.char_conditional_branch_bne(target, iterations)
        actual_result_json = json.loads(actual_result)
        expected_result_json = load_test_data("char_conditional_branch_bne")
        utils.compare_json_data(actual_result_json, expected_result_json, ignored_keys_set)

    def test_char_csr_read(self):
        actual_result = fi_ibex_functions.char_csr_read(target, iterations)
        actual_result_json = json.loads(actual_result)
        expected_result_json = load_test_data("char_csr_read")
        utils.compare_json_data(actual_result_json, expected_result_json, ignored_keys_set)

    def test_char_csr_write(self):
        actual_result = fi_ibex_functions.char_csr_write(target, iterations)
        actual_result_json = json.loads(actual_result)
        expected_result_json = load_test_data("char_csr_write")
        utils.compare_json_data(actual_result_json, expected_result_json, ignored_keys_set)

    @unittest.skip
    def test_char_csr_combi(self):
        ref_values = [
            1,
            5,
            33,
            101,
            3,
            5,
            39321,
            6,
            5138,
            50115,
            39321,
            38502,
            39321,
            39321,
            1,
            2,
            3,
        ]
        actual_result = fi_ibex_functions.char_csr_combi(
            target, trigger=0, ref_values=ref_values, iterations=iterations
        )
        actual_result_json = json.loads(actual_result)
        expected_result_json = json.loads(
            '{"output":[1,5,33,101,3,5,39321,6,5138,50115,39321,38502,39321,39321,1,2,3], \
                "data_faulty": [false,false,false,false,false,false,false,false,false,false, \
                false,false,false,false,false,false,false],"err_status":0,"alerts":[0,0,0], \
                "loc_alerts":0,"ast_alerts":[0,0]}'
        )
        utils.compare_json_data(actual_result_json, expected_result_json, ignored_keys_set)

        # Reset to allow the next test to start fresh
        target.reset_target()
        target.dump_all()

        ref_values = [
            2,
            3,
            16641,
            4,
            5,
            6,
            38553,
            7,
            5137,
            256,
            26214,
            26214,
            26214,
            5,
            2,
            3,
            4,
        ]
        actual_result = fi_ibex_functions.char_csr_combi(
            target, trigger=0, ref_values=ref_values, iterations=iterations
        )
        actual_result_json = json.loads(actual_result)
        expected_result_json = json.loads(
            '{"output":[2,3,16641,4,5,6,38553,7,5137,256,26214,26214,26214,5,2,3,4], \
                "data_faulty": \
                [false,false,false,false,false,false,false,false,false,false,false,false,false,\
                false,false,false,false],"err_status":0,"alerts":[0,0,0],"loc_alerts":0,\
                "ast_alerts":[0,0]}'
        )
        utils.compare_json_data(actual_result_json, expected_result_json, ignored_keys_set)

        # Reset to allow other tests to start again
        target.reset_target()
        target.dump_all()

    @unittest.skip
    def test_char_flash_read(self):
        for flash_region in range(2, 10):
            actual_result = fi_ibex_functions.char_flash_read(
                target, flash_region=flash_region, iterations=iterations
            )
            actual_result_json = json.loads(actual_result)
            expected_result_json = load_test_data("char_flash_read")
            if "success" not in actual_result_json:
                utils.compare_json_data(actual_result_json, expected_result_json, ignored_keys_set)

    @unittest.skip
    def test_char_flash_read_static(self):
        test_succeeded = False
        for flash_region in range(2, 10):
            actual_result = fi_ibex_functions.char_flash_read_static(
                target, init=True, flash_region=flash_region, iterations=iterations
            )
            actual_result_json = json.loads(actual_result)
            expected_result_json = load_test_data("char_flash_read_static")
            if "success" not in actual_result_json:
                utils.compare_json_data(actual_result_json, expected_result_json, ignored_keys_set)

                actual_result = fi_ibex_functions.char_flash_read_static(
                    target, init=False, flash_region=flash_region, iterations=iterations
                )
                actual_result_json = json.loads(actual_result)
                utils.compare_json_data(actual_result_json, expected_result_json, ignored_keys_set)

                test_succeeded = True
        assert test_succeeded, "No writable flash region found"

    @unittest.skip
    def test_char_flash_write(self):
        for flash_region in range(2, 10):
            actual_result = fi_ibex_functions.char_flash_write(
                target, flash_region=flash_region, iterations=iterations
            )
            actual_result_json = json.loads(actual_result)
            expected_result_json = load_test_data("char_flash_write")
            if "success" not in actual_result_json:
                utils.compare_json_data(actual_result_json, expected_result_json, ignored_keys_set)

    def test_char_mem_op_loop(self):
        actual_result = fi_ibex_functions.char_mem_op_loop(target, iterations)
        actual_result_json = json.loads(actual_result)
        expected_result_json = load_test_data("char_mem_op_loop")
        utils.compare_json_data(actual_result_json, expected_result_json, ignored_keys_set)

    def test_char_register_file(self):
        actual_result = fi_ibex_functions.char_register_file(target, iterations)
        actual_result_json = json.loads(actual_result)
        expected_result_json = load_test_data("char_register_file")
        utils.compare_json_data(actual_result_json, expected_result_json, ignored_keys_set)

    def test_char_register_file_read(self):
        actual_result = fi_ibex_functions.char_register_file_read(target, iterations)
        actual_result_json = json.loads(actual_result)
        expected_result_json = load_test_data("char_register_file_read")
        utils.compare_json_data(actual_result_json, expected_result_json, ignored_keys_set)

    def test_char_reg_op_loop(self):
        actual_result = fi_ibex_functions.char_reg_op_loop(target, iterations)
        actual_result_json = json.loads(actual_result)
        expected_result_json = load_test_data("char_reg_op_loop")
        utils.compare_json_data(actual_result_json, expected_result_json, ignored_keys_set)

    def test_char_single_beq(self):
        actual_result = fi_ibex_functions.char_single_beq(target, iterations)
        actual_result_json = json.loads(actual_result)
        expected_result_json = load_test_data("char_single_beq")
        utils.compare_json_data(actual_result_json, expected_result_json, ignored_keys_set)

    def test_char_single_bne(self):
        actual_result = fi_ibex_functions.char_single_bne(target, iterations)
        actual_result_json = json.loads(actual_result)
        expected_result_json = load_test_data("char_single_bne")
        utils.compare_json_data(actual_result_json, expected_result_json, ignored_keys_set)

    def test_char_sram_read(self):
        actual_result = fi_ibex_functions.char_sram_read(target, iterations)
        actual_result_json = json.loads(actual_result)
        expected_result_json = load_test_data("char_sram_read")
        utils.compare_json_data(actual_result_json, expected_result_json, ignored_keys_set)

    def test_char_sram_read_ret(self):
        actual_result = fi_ibex_functions.char_sram_read_ret(target, iterations)
        actual_result_json = json.loads(actual_result)
        expected_result_json = load_test_data("char_sram_read_ret")
        utils.compare_json_data(actual_result_json, expected_result_json, ignored_keys_set)

    @unittest.skip
    def test_char_sram_static(self):
        actual_result = fi_ibex_functions.char_sram_static(target, iterations)
        actual_result_json = json.loads(actual_result)
        expected_result_json = load_test_data("char_sram_static")
        utils.compare_json_data(actual_result_json, expected_result_json, ignored_keys_set)

    def test_char_sram_write(self):
        actual_result = fi_ibex_functions.char_sram_write(target, iterations)
        actual_result_json = json.loads(actual_result)
        expected_result_json = load_test_data("char_sram_write")
        utils.compare_json_data(actual_result_json, expected_result_json, ignored_keys_set)

    def test_char_sram_write_read(self):
        actual_result = fi_ibex_functions.char_sram_write_read(target, iterations)
        actual_result_json = json.loads(actual_result)
        expected_result_json = load_test_data("char_sram_write_read")
        utils.compare_json_data(actual_result_json, expected_result_json, ignored_keys_set)

    def test_char_sram_write_read_alt(self):
        actual_result = fi_ibex_functions.char_sram_write_read_alt(target, iterations)
        actual_result_json = json.loads(actual_result)
        expected_result_json = load_test_data("char_sram_write_read_alt")
        utils.compare_json_data(actual_result_json, expected_result_json, ignored_keys_set)

    def test_char_sram_write_static_unrolled(self):
        actual_result = fi_ibex_functions.char_sram_write_static_unrolled(target, iterations)
        actual_result_json = json.loads(actual_result)
        expected_result_json = load_test_data("char_sram_write_static_unrolled")
        utils.compare_json_data(actual_result_json, expected_result_json, ignored_keys_set)

    def test_char_unconditional_branch(self):
        actual_result = fi_ibex_functions.char_unconditional_branch(target, iterations)
        actual_result_json = json.loads(actual_result)
        expected_result_json = load_test_data("char_unconditional_branch")
        utils.compare_json_data(actual_result_json, expected_result_json, ignored_keys_set)

    def test_char_unconditional_branch_nop(self):
        actual_result = fi_ibex_functions.char_unconditional_branch_nop(target, iterations)
        actual_result_json = json.loads(actual_result)
        expected_result_json = load_test_data("char_unconditional_branch_nop")
        utils.compare_json_data(actual_result_json, expected_result_json, ignored_keys_set)

    def test_char_unrolled_mem_op_loop(self):
        actual_result = fi_ibex_functions.char_unrolled_mem_op_loop(target, iterations)
        actual_result_json = json.loads(actual_result)
        expected_result_json = load_test_data("char_unrolled_mem_op_loop")
        utils.compare_json_data(actual_result_json, expected_result_json, ignored_keys_set)

    def test_char_unrolled_reg_op_loop(self):
        actual_result = fi_ibex_functions.char_unrolled_reg_op_loop(target, iterations)
        actual_result_json = json.loads(actual_result)
        expected_result_json = load_test_data("char_unrolled_reg_op_loop")
        utils.compare_json_data(actual_result_json, expected_result_json, ignored_keys_set)

    def test_char_unrolled_reg_op_loop_chain(self):
        actual_result = fi_ibex_functions.char_unrolled_reg_op_loop_chain(target, iterations)
        actual_result_json = json.loads(actual_result)
        expected_result_json = load_test_data("char_unrolled_reg_op_loop_chain")
        utils.compare_json_data(actual_result_json, expected_result_json, ignored_keys_set)

    @unittest.skip
    def test_char_otp_data_read(self):
        actual_result = fi_ibex_functions.char_otp_data_read(target, iterations)
        actual_result_json = json.loads(actual_result)
        expected_result_json = load_test_data("char_otp_data_read")
        utils.compare_json_data(actual_result_json, expected_result_json, ignored_keys_set)

        # Reset to allow other tests to start again
        target.reset_target()
        target.dump_all()

    @unittest.skip
    def test_char_otp_read_lock(self):
        actual_result = fi_ibex_functions.char_otp_read_lock(target, iterations)
        actual_result_json = json.loads(actual_result)
        expected_result_json = load_test_data("char_otp_read_lock")
        utils.compare_json_data(actual_result_json, expected_result_json, ignored_keys_set)

        # Reset to allow other tests to start again
        target.reset_target()
        target.dump_all()

    def test_char_addi_single_beq_cm(self):
        actual_result, status = fi_ibex_functions.char_addi_single_beq_cm(target, reset=True)
        self.assertIn("FAULT", actual_result)

        # Reset to allow other tests to start again
        target.reset_target()
        target.dump_all()

    @unittest.skip
    def test_char_addi_single_beq_cm2(self):
        actual_result, status = fi_ibex_functions.char_addi_single_beq_cm2(target)
        self.assertIn("FAULT", actual_result)

        # Reset to allow other tests to start again
        target.reset_target()
        target.dump_all()

    @unittest.skip
    def test_char_hardened_check_eq_complement_branch(self):
        actual_result, status = fi_ibex_functions.char_hardened_check_eq_complement_branch(target)
        self.assertIn("FAULT", actual_result)

        # Reset to allow other tests to start again
        target.reset_target()
        target.dump_all()

    @unittest.skip
    def test_char_hardened_check_eq_unimp(self):
        actual_result, status = fi_ibex_functions.char_hardened_check_eq_unimp(target)
        self.assertIn("FAULT", actual_result)

        # Reset to allow other tests to start again
        target.reset_target()
        target.dump_all()

    @unittest.skip
    def test_char_hardened_check_eq_2_unimps(self):
        actual_result, status = fi_ibex_functions.char_hardened_check_eq_2_unimps(target)
        self.assertIn("FAULT", actual_result)

        # Reset to allow other tests to start again
        target.reset_target()
        target.dump_all()

    @unittest.skip
    def test_char_hardened_check_eq_3_unimps(self):
        actual_result, status = fi_ibex_functions.char_hardened_check_eq_3_unimps(target)
        self.assertIn("FAULT", actual_result)

        # Reset to allow other tests to start again
        target.reset_target()
        target.dump_all()

    @unittest.skip
    def test_char_hardened_check_eq_4_unimps(self):
        actual_result, status = fi_ibex_functions.char_hardened_check_eq_4_unimps(target)
        self.assertIn("FAULT", actual_result)

        # Reset to allow other tests to start again
        target.reset_target()
        target.dump_all()

    @unittest.skip
    def test_char_hardened_check_eq_5_unimps(self):
        actual_result, status = fi_ibex_functions.char_hardened_check_eq_5_unimps(target)
        self.assertIn("FAULT", actual_result)

        # Reset to allow other tests to start again
        target.reset_target()
        target.dump_all()


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
