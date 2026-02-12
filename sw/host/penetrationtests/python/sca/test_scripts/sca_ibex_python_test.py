# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from sw.host.penetrationtests.python.sca.host_scripts import sca_ibex_functions
from sw.host.penetrationtests.python.sca.communication.sca_ibex_commands import OTIbex
from python.runfiles import Runfiles
from sw.host.penetrationtests.python.util import targets
from sw.host.penetrationtests.python.util import utils
import json
import random
import unittest
import argparse
import sys

ignored_keys_set = set([])
opentitantool_path = ""
iterations = 2
num_segments_list = [1, 5, 12]

target = None

# Read in the extra arguments from the opentitan_test.
parser = argparse.ArgumentParser()
parser.add_argument("--bitstream", type=str)
parser.add_argument("--bootstrap", type=str)

args, config_args = parser.parse_known_args()

BITSTREAM = args.bitstream
BOOTSTRAP = args.bootstrap


class IbexScaTest(unittest.TestCase):

    def test_init(self):
        ibexsca = OTIbex(target)
        device_id, owner_page, boot_log, boot_measurements, version = ibexsca.init()
        device_id_json = json.loads(device_id)
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

        self.assertEqual(
            expected_boot_log_keys, actual_boot_log_keys, "boot_log keys do not match"
        )

        expected_boot_measurements_keys = {"bl0", "rom_ext"}
        actual_boot_measurements_keys = set(boot_measurements_json.keys())

        self.assertEqual(
            expected_boot_measurements_keys,
            actual_boot_measurements_keys,
            "boot_measurements keys do not match",
        )

        self.assertIn("PENTEST", version)

    def test_char_combi_operations_batch(self):
        for num_segments in num_segments_list:
            trigger = 0
            fixed_data1 = 11
            fixed_data2 = 11
            actual_result = sca_ibex_functions.char_combi_operations_batch(
                target,
                iterations,
                num_segments,
                trigger,
                fixed_data1,
                fixed_data2,
            )
            actual_result_json = json.loads(actual_result)

            expected_result_json = json.loads('{"result":[0,0,0,0,0,0,0,0,0,0,0,0]}')
            utils.compare_json_data(
                actual_result_json, expected_result_json, ignored_keys_set
            )

            trigger = 32
            fixed_data1 = 11
            fixed_data2 = 11
            actual_result = sca_ibex_functions.char_combi_operations_batch(
                target,
                iterations,
                num_segments,
                trigger,
                fixed_data1,
                fixed_data2,
            )
            actual_result_json = json.loads(actual_result)

            xor = fixed_data1 ^ fixed_data2
            add = (fixed_data1 + fixed_data2) & 0xFFFFFFFF
            sub = (fixed_data1 - fixed_data2) & 0xFFFFFFFF
            shift_operand = (fixed_data2 & 0xFFFFFFFF) % 32
            shift = (fixed_data1 << shift_operand) & 0xFFFFFFFF | (
                fixed_data1 >> (32 - shift_operand) & 0xFFFFFFFF
            )
            mult = (fixed_data1 * fixed_data2) & 0xFFFFFFFF
            if fixed_data2 == 0:
                div = 0xFFFFFFFF
            elif (
                utils.to_signed32(fixed_data1) == -2147483648 and
                utils.to_signed32(fixed_data2) == -1
            ):
                div = 0x80000000
            else:
                div = (
                    int(utils.to_signed32(fixed_data1) / utils.to_signed32(fixed_data2)) &
                    0xFFFFFFFF
                )

            expected_result_json = {"result": [0, 0, 0, 0, 0, div, 0, 0, 0, 0, 0, 0]}
            utils.compare_json_data(
                actual_result_json, expected_result_json, ignored_keys_set
            )

            trigger = 256
            fixed_data1 = 11
            fixed_data2 = 11
            actual_result = sca_ibex_functions.char_combi_operations_batch(
                target,
                iterations,
                num_segments,
                trigger,
                fixed_data1,
                fixed_data2,
            )
            actual_result_json = json.loads(actual_result)

            expected_result_json = {
                "result": [0, 0, 0, 0, 0, 0, 0, 0, fixed_data2, 0, 0, 0]
            }
            utils.compare_json_data(
                actual_result_json, expected_result_json, ignored_keys_set
            )

            trigger = 4095
            fixed_data1 = 11
            fixed_data2 = 11
            actual_result = sca_ibex_functions.char_combi_operations_batch(
                target,
                iterations,
                num_segments,
                trigger,
                fixed_data1,
                fixed_data2,
            )
            actual_result_json = json.loads(actual_result)

            xor = fixed_data1 ^ fixed_data2
            add = (fixed_data1 + fixed_data2) & 0xFFFFFFFF
            sub = (fixed_data1 - fixed_data2) & 0xFFFFFFFF
            shift_operand = (fixed_data2 & 0xFFFFFFFF) % 32
            shift = (fixed_data1 << shift_operand) & 0xFFFFFFFF | (
                fixed_data1 >> (32 - shift_operand) & 0xFFFFFFFF
            )
            mult = (fixed_data1 * fixed_data2) & 0xFFFFFFFF
            if fixed_data2 == 0:
                div = 0xFFFFFFFF
            elif (
                utils.to_signed32(fixed_data1) == -2147483648 and
                utils.to_signed32(fixed_data2) == -1
            ):
                div = 0x80000000
            else:
                div = (
                    int(utils.to_signed32(fixed_data1) / utils.to_signed32(fixed_data2)) &
                    0xFFFFFFFF
                )

            expected_result_json = {
                "result": [
                    xor,
                    add,
                    sub,
                    shift,
                    mult,
                    div,
                    fixed_data1,
                    fixed_data1,
                    fixed_data2,
                    fixed_data2,
                    fixed_data2,
                    fixed_data2,
                ]
            }
            utils.compare_json_data(
                actual_result_json, expected_result_json, ignored_keys_set
            )

    def test_char_combi_operations_batch_fvsr(self):
        for num_segments in num_segments_list:
            # Seed the synchronized randomness with the same seed as in the chip which is 1
            random.seed(1)

            trigger = 0
            fixed_data1 = 11
            fixed_data2 = 11
            actual_result = sca_ibex_functions.char_combi_operations_batch_fvsr(
                target,
                iterations,
                num_segments,
                trigger,
                fixed_data1,
                fixed_data2,
            )
            actual_result_json = json.loads(actual_result)

            # Calculate the expected result
            for _ in range(iterations):
                sample_fixed = True
                for __ in range(num_segments):
                    if sample_fixed:
                        batch_data1 = fixed_data1
                    else:
                        batch_data1 = random.getrandbits(32)
                    sample_fixed = random.getrandbits(32) & 0x1

                sample_fixed = True
                for __ in range(num_segments):
                    if sample_fixed:
                        batch_data2 = fixed_data2
                    else:
                        batch_data2 = random.getrandbits(32)
                    sample_fixed = random.getrandbits(32) & 0x1

            expected_result_json = json.loads('{"result":[0,0,0,0,0,0,0,0,0,0,0,0]}')
            utils.compare_json_data(
                actual_result_json, expected_result_json, ignored_keys_set
            )

            # Seed the synchronized randomness with the same seed as in the chip which is 1
            random.seed(1)

            trigger = 32
            fixed_data1 = 11
            fixed_data2 = 11
            actual_result = sca_ibex_functions.char_combi_operations_batch_fvsr(
                target,
                iterations,
                num_segments,
                trigger,
                fixed_data1,
                fixed_data2,
            )
            actual_result_json = json.loads(actual_result)

            # Calculate the expected result
            for _ in range(iterations):
                sample_fixed = True
                for __ in range(num_segments):
                    if sample_fixed:
                        batch_data1 = fixed_data1
                    else:
                        batch_data1 = random.getrandbits(32)
                    sample_fixed = random.getrandbits(32) & 0x1

                sample_fixed = True
                for __ in range(num_segments):
                    if sample_fixed:
                        batch_data2 = fixed_data2
                    else:
                        batch_data2 = random.getrandbits(32)
                    sample_fixed = random.getrandbits(32) & 0x1

            batch_data1 = utils.to_signed32(batch_data1)
            batch_data2 = utils.to_signed32(batch_data2)
            if batch_data2 == 0:
                div = 0xFFFFFFFF
            elif batch_data1 == -2147483648 and batch_data2 == -1:
                div = 0x80000000
            else:
                div = int(batch_data1 / batch_data2) & 0xFFFFFFFF

            expected_result_json = {"result": [0, 0, 0, 0, 0, div, 0, 0, 0, 0, 0, 0]}
            utils.compare_json_data(
                actual_result_json, expected_result_json, ignored_keys_set
            )

            # Seed the synchronized randomness with the same seed as in the chip which is 1
            random.seed(1)

            trigger = 256
            fixed_data1 = 11
            fixed_data2 = 11
            actual_result = sca_ibex_functions.char_combi_operations_batch_fvsr(
                target,
                iterations,
                num_segments,
                trigger,
                fixed_data1,
                fixed_data2,
            )
            actual_result_json = json.loads(actual_result)

            # Calculate the expected result
            for _ in range(iterations):
                sample_fixed = True
                for __ in range(num_segments):
                    if sample_fixed:
                        batch_data1 = fixed_data1
                    else:
                        batch_data1 = random.getrandbits(32)
                    sample_fixed = random.getrandbits(32) & 0x1

                sample_fixed = True
                for __ in range(num_segments):
                    if sample_fixed:
                        batch_data2 = fixed_data2
                    else:
                        batch_data2 = random.getrandbits(32)
                    sample_fixed = random.getrandbits(32) & 0x1

            expected_result_json = {
                "result": [0, 0, 0, 0, 0, 0, 0, 0, batch_data2, 0, 0, 0]
            }
            utils.compare_json_data(
                actual_result_json, expected_result_json, ignored_keys_set
            )

            # Seed the synchronized randomness with the same seed as in the chip which is 1
            random.seed(1)

            trigger = 4095
            fixed_data1 = 11
            fixed_data2 = 11
            actual_result = sca_ibex_functions.char_combi_operations_batch_fvsr(
                target,
                iterations,
                num_segments,
                trigger,
                fixed_data1,
                fixed_data2,
            )
            actual_result_json = json.loads(actual_result)

            # Calculate the expected result
            for _ in range(iterations):
                sample_fixed = True
                for __ in range(num_segments):
                    if sample_fixed:
                        batch_data1 = fixed_data1
                    else:
                        batch_data1 = random.getrandbits(32)
                    sample_fixed = random.getrandbits(32) & 0x1

                sample_fixed = True
                for __ in range(num_segments):
                    if sample_fixed:
                        batch_data2 = fixed_data2
                    else:
                        batch_data2 = random.getrandbits(32)
                    sample_fixed = random.getrandbits(32) & 0x1

            xor = batch_data1 ^ batch_data2
            add = (batch_data1 + batch_data2) & 0xFFFFFFFF
            sub = (batch_data1 - batch_data2) & 0xFFFFFFFF
            shift_operand = (batch_data2 & 0xFFFFFFFF) % 32
            shift = (batch_data1 << shift_operand) & 0xFFFFFFFF | (
                batch_data1 >> (32 - shift_operand) & 0xFFFFFFFF
            )
            mult = (batch_data1 * batch_data2) & 0xFFFFFFFF
            if batch_data2 == 0:
                div = 0xFFFFFFFF
            elif (
                utils.to_signed32(batch_data1) == -2147483648 and
                utils.to_signed32(batch_data2) == -1
            ):
                div = 0x80000000
            else:
                div = (
                    int(utils.to_signed32(batch_data1) / utils.to_signed32(batch_data2)) &
                    0xFFFFFFFF
                )

            expected_result_json = {
                "result": [
                    xor,
                    add,
                    sub,
                    shift,
                    mult,
                    div,
                    batch_data1,
                    batch_data1,
                    batch_data2,
                    batch_data2,
                    batch_data2,
                    batch_data2,
                ]
            }
            utils.compare_json_data(
                actual_result_json, expected_result_json, ignored_keys_set
            )

            return True

    def test_char_register_file_read(self):
        data = [7, 6, 5, 4, 3, 2, 1, 0]
        actual_result = sca_ibex_functions.char_register_file_read(target, iterations, data)
        actual_result_json = json.loads(actual_result)
        expected_result_json = json.loads('{"result":0}')
        utils.compare_json_data(actual_result_json, expected_result_json, ignored_keys_set)

    def test_char_register_file_read_batch_fvsr(self):
        for num_segments in num_segments_list:
            fixed_data = 2048
            actual_result = sca_ibex_functions.char_register_file_read_batch_fvsr(
                target, iterations, fixed_data, num_segments
            )
            actual_result_json = json.loads(actual_result)

            # Seed the synchronized randomness with the same seed as in the chip which is 1
            random.seed(1)

            # Generate the batch data
            for _ in range(iterations):
                sample_fixed = True
                for __ in range(num_segments):
                    if sample_fixed:
                        batch_data = fixed_data
                    else:
                        batch_data = random.getrandbits(32)
                    sample_fixed = random.getrandbits(32) & 0x1
            expected_result_json = {"result": batch_data}
            utils.compare_json_data(
                actual_result_json, expected_result_json, ignored_keys_set
            )

    def test_char_register_file_read_batch_random(self):
        for num_segments in num_segments_list:
            actual_result = sca_ibex_functions.char_register_file_read_batch_random(
                target, iterations, num_segments
            )
            actual_result_json = json.loads(actual_result)

            # Seed the synchronized randomness with the same seed as in the chip which is 1
            random.seed(1)

            # Generate the batch data
            for _ in range(iterations):
                for __ in range(num_segments):
                    batch_data = random.getrandbits(32)
            expected_result_json = {"result": batch_data}
            utils.compare_json_data(
                actual_result_json, expected_result_json, ignored_keys_set
            )

    def test_char_register_file_write(self):
        data = [7, 6, 5, 4, 3, 2, 1, 0]
        actual_result = sca_ibex_functions.char_register_file_write(target, iterations, data)
        actual_result_json = json.loads(actual_result)
        expected_result_json = json.loads('{"result":0}')
        utils.compare_json_data(actual_result_json, expected_result_json, ignored_keys_set)

    def test_char_register_file_write_batch_fvsr(self):
        for num_segments in num_segments_list:
            fixed_data = 2048
            actual_result = sca_ibex_functions.char_register_file_write_batch_fvsr(
                target, iterations, fixed_data, num_segments
            )
            actual_result_json = json.loads(actual_result)

            # Seed the synchronized randomness with the same seed as in the chip which is 1
            random.seed(1)

            # Generate the batch data
            for _ in range(iterations):
                sample_fixed = True
                for __ in range(num_segments):
                    if sample_fixed:
                        batch_data = fixed_data
                    else:
                        batch_data = random.getrandbits(32)
                    sample_fixed = random.getrandbits(32) & 0x1
            expected_result_json = {"result": batch_data}
            utils.compare_json_data(
                actual_result_json, expected_result_json, ignored_keys_set
            )

    def test_char_register_file_write_batch_random(self):
        for num_segments in num_segments_list:
            actual_result = sca_ibex_functions.char_register_file_write_batch_random(
                target, iterations, num_segments
            )
            actual_result_json = json.loads(actual_result)

            # Seed the synchronized randomness with the same seed as in the chip which is 1
            random.seed(1)

            # Generate the batch data
            for _ in range(iterations):
                # We generate random data
                for __ in range(num_segments):
                    batch_data = random.getrandbits(32)
            expected_result_json = {"result": batch_data}
            utils.compare_json_data(
                actual_result_json, expected_result_json, ignored_keys_set
            )

    def test_char_tl_read(self):
        data = [255, 255, 255, 0, 0, 0, 0, 0]
        actual_result = sca_ibex_functions.char_tl_read(target, iterations, data)
        actual_result_json = json.loads(actual_result)
        expected_result_json = json.loads('{"result":0}')
        utils.compare_json_data(actual_result_json, expected_result_json, ignored_keys_set)

    def test_char_tl_read_batch_fvsr(self):
        for num_segments in num_segments_list:
            fixed_data = 2048
            actual_result = sca_ibex_functions.char_tl_read_batch_fvsr(
                target, iterations, fixed_data, num_segments
            )
            actual_result_json = json.loads(actual_result)

            # Seed the synchronized randomness with the same seed as in the chip which is 1
            random.seed(1)

            # Generate the batch data
            for _ in range(iterations):
                sample_fixed = True
                for __ in range(num_segments):
                    if sample_fixed:
                        batch_data = fixed_data
                    else:
                        batch_data = random.getrandbits(32)
                    sample_fixed = random.getrandbits(32) & 0x1
            expected_result_json = {"result": batch_data}
            utils.compare_json_data(
                actual_result_json, expected_result_json, ignored_keys_set
            )

    def test_char_tl_read_batch_fvsr_fix_address(self):
        for num_segments in num_segments_list:
            fixed_data = 2048
            actual_result = sca_ibex_functions.char_tl_read_batch_fvsr_fix_address(
                target, iterations, fixed_data, num_segments
            )
            actual_result_json = json.loads(actual_result)

            # Seed the synchronized randomness with the same seed as in the chip which is 1
            random.seed(1)

            # Generate the batch data
            for _ in range(iterations):
                sample_fixed = True
                for __ in range(num_segments):
                    if sample_fixed:
                        batch_data = fixed_data
                    else:
                        batch_data = random.getrandbits(32)
                    sample_fixed = random.getrandbits(32) & 0x1
            expected_result_json = {"result": batch_data}
            utils.compare_json_data(
                actual_result_json, expected_result_json, ignored_keys_set
            )

    def test_char_tl_read_batch_random(self):
        for num_segments in num_segments_list:
            actual_result = sca_ibex_functions.char_tl_read_batch_random(
                target, iterations, num_segments
            )
            actual_result_json = json.loads(actual_result)

            # Seed the synchronized randomness with the same seed as in the chip which is 1
            random.seed(1)

            # Generate the batch data
            for _ in range(iterations):
                for __ in range(num_segments):
                    batch_data = random.getrandbits(32)
            expected_result_json = {"result": batch_data}
            utils.compare_json_data(
                actual_result_json, expected_result_json, ignored_keys_set
            )

    def test_char_tl_read_batch_random_fix_address(self):
        for num_segments in num_segments_list:
            actual_result = sca_ibex_functions.char_tl_read_batch_random_fix_address(
                target, iterations, num_segments
            )
            actual_result_json = json.loads(actual_result)

            # Seed the synchronized randomness with the same seed as in the chip which is 1
            random.seed(1)

            # Generate the batch data
            for _ in range(iterations):
                for __ in range(num_segments):
                    batch_data = random.getrandbits(32)
            expected_result_json = {"result": batch_data}
            utils.compare_json_data(
                actual_result_json, expected_result_json, ignored_keys_set
            )

    def test_char_tl_write(self):
        data = [255, 255, 255, 0, 0, 0, 0, 0]
        actual_result = sca_ibex_functions.char_tl_write(target, iterations, data)
        actual_result_json = json.loads(actual_result)
        expected_result_json = json.loads('{"result":0}')
        utils.compare_json_data(actual_result_json, expected_result_json, ignored_keys_set)

    def test_char_tl_write_batch_fvsr(self):
        for num_segments in num_segments_list:
            fixed_data = 2048
            actual_result = sca_ibex_functions.char_tl_write_batch_fvsr(
                target, iterations, fixed_data, num_segments
            )
            actual_result_json = json.loads(actual_result)

            # Seed the synchronized randomness with the same seed as in the chip which is 1
            random.seed(1)

            # Generate the batch data
            for _ in range(iterations):
                sample_fixed = True
                for __ in range(num_segments):
                    if sample_fixed:
                        batch_data = fixed_data
                    else:
                        batch_data = random.getrandbits(32)
                    sample_fixed = random.getrandbits(32) & 0x1
            expected_result_json = {"result": batch_data}
            utils.compare_json_data(
                actual_result_json, expected_result_json, ignored_keys_set
            )

    def test_char_tl_write_batch_fvsr_fix_address(self):
        for num_segments in num_segments_list:
            fixed_data = 2048
            actual_result = sca_ibex_functions.char_tl_write_batch_fvsr_fix_address(
                target, iterations, fixed_data, num_segments
            )
            actual_result_json = json.loads(actual_result)

            # Seed the synchronized randomness with the same seed as in the chip which is 1
            random.seed(1)

            # Generate the batch data
            for _ in range(iterations):
                sample_fixed = True
                for __ in range(num_segments):
                    if sample_fixed:
                        batch_data = fixed_data
                    else:
                        batch_data = random.getrandbits(32)
                    sample_fixed = random.getrandbits(32) & 0x1
            expected_result_json = {"result": batch_data}
            utils.compare_json_data(
                actual_result_json, expected_result_json, ignored_keys_set
            )

    def test_char_tl_write_batch_random(self):
        for num_segments in num_segments_list:
            actual_result = sca_ibex_functions.char_tl_write_batch_random(
                target, iterations, num_segments
            )
            actual_result_json = json.loads(actual_result)

            # Seed the synchronized randomness with the same seed as in the chip which is 1
            random.seed(1)

            # Generate the batch data
            for _ in range(iterations):
                for __ in range(num_segments):
                    batch_data = random.getrandbits(32)
            expected_result_json = {"result": batch_data}
            utils.compare_json_data(
                actual_result_json, expected_result_json, ignored_keys_set
            )

    def test_char_tl_write_batch_random_fix_address(self):
        for num_segments in num_segments_list:
            actual_result = sca_ibex_functions.char_tl_write_batch_random_fix_address(
                target, iterations, num_segments
            )
            actual_result_json = json.loads(actual_result)

            # Seed the synchronized randomness with the same seed as in the chip which is 1
            random.seed(1)

            # Generate the batch data
            for _ in range(iterations):
                for __ in range(num_segments):
                    batch_data = random.getrandbits(32)
            expected_result_json = {"result": batch_data}
            utils.compare_json_data(
                actual_result_json, expected_result_json, ignored_keys_set
            )


if __name__ == "__main__":
    r = Runfiles.Create()
    # Get the opentitantool path.
    opentitantool_path = r.Rlocation(
        "lowrisc_opentitan/sw/host/opentitantool/opentitantool"
    )
    # Program the bitstream for FPGAs.
    bitstream_path = None
    if BITSTREAM:
        bitstream_path = r.Rlocation(
            "lowrisc_opentitan/" + BITSTREAM
        )
    # Get the firmware path.
    firmware_path = r.Rlocation(
        "lowrisc_opentitan/" + BOOTSTRAP
    )

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
        tool_args=config_args
    )

    target = targets.Target(target_cfg)

    target.initialize_target()

    unittest.main(argv=[sys.argv[0]])
