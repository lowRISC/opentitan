# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from sw.host.penetrationtests.python.sca.host_scripts import sca_aes_functions
from sw.host.penetrationtests.python.sca.communication.sca_aes_commands import OTAES
from python.runfiles import Runfiles
from sw.host.penetrationtests.python.util import targets
from sw.host.penetrationtests.python.util import utils
import json
import random
from Crypto.Cipher import AES
import unittest
import argparse
import sys


ignored_keys_set = set([])
opentitantool_path = ""
iterations = 2
num_segments_list = [1, 5, 12]
# For testing, we only use the software trigger
fpga = 0

target = None

# Read in the extra arguments from the opentitan_test.
parser = argparse.ArgumentParser()
parser.add_argument("--bitstream", type=str)
parser.add_argument("--bootstrap", type=str)

args, config_args = parser.parse_known_args()

BITSTREAM = args.bitstream
BOOTSTRAP = args.bootstrap


class AesScaTest(unittest.TestCase):

    def test_init(self):
        aessca = OTAES(target)
        device_id, owner_page, boot_log, boot_measurements, version = aessca.init(fpga)
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

    def test_char_aes_single_encrypt(self):
        # Note that setting this to false gives errors for production chips
        masking = True
        key = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
        text = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
        actual_result = sca_aes_functions.char_aes_single_encrypt(
            target, iterations, fpga, masking, key, text
        )
        actual_result_json = json.loads(actual_result)

        cipher_gen = AES.new(bytes(key), AES.MODE_ECB)
        expected_result = [x for x in cipher_gen.encrypt(bytes(text))]

        expected_result_json = {"ciphertext": expected_result, "ciphertext_length": 16}
        utils.compare_json_data(
            actual_result_json, expected_result_json, ignored_keys_set
        )

    def test_char_aes_batch_daisy_chain(self):
        for num_segments in num_segments_list:
            # Note that setting this to false gives errors for production chips
            masking = True
            key = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
            text = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
            actual_result = sca_aes_functions.char_aes_batch_daisy_chain(
                target, iterations, num_segments, fpga, masking, key, text
            )
            actual_result_json = json.loads(actual_result)

            cipher_gen = AES.new(bytes(key), AES.MODE_ECB)
            for _ in range(iterations):
                chained_text = text
                for __ in range(num_segments):
                    chained_text = [x for x in cipher_gen.encrypt(bytes(chained_text))]

            expected_result_json = {
                "ciphertext": chained_text,
                "ciphertext_length": len(chained_text),
            }
            utils.compare_json_data(
                actual_result_json, expected_result_json, ignored_keys_set
            )

    def test_char_aes_batch_fvsr_data(self):
        for num_segments in num_segments_list:
            # Note that setting this to false gives errors for production chips
            masking = True
            key = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
            text = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
            actual_result = sca_aes_functions.char_aes_batch_fvsr_data(
                target, iterations, num_segments, fpga, masking, key, text
            )
            actual_result_json = json.loads(actual_result)

            # Set the synchronized randomness
            batch_prng_seed = 1
            random.seed(batch_prng_seed)

            # Generate the batch data
            for _ in range(iterations):
                sample_fixed = 1
                for __ in range(num_segments):
                    if sample_fixed == 1:
                        batch_data = text
                    else:
                        batch_data = [random.randint(0, 255) for _ in range(len(text))]
                    sample_fixed = random.randint(0, 255) & 0x1

            cipher_gen = AES.new(bytes(key), AES.MODE_ECB)
            expected_result = [x for x in cipher_gen.encrypt(bytes(batch_data))]

            expected_result_json = {
                "ciphertext": expected_result,
                "ciphertext_length": len(expected_result),
            }
            utils.compare_json_data(
                actual_result_json, expected_result_json, ignored_keys_set
            )

    def test_char_aes_batch_fvsr_key(self):
        for num_segments in num_segments_list:
            masking = True
            key = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
            actual_result = sca_aes_functions.char_aes_batch_fvsr_key(
                target, iterations, num_segments, fpga, masking, key
            )
            actual_result_json = json.loads(actual_result)

            # Set the synchronized randomness
            batch_prng_seed = 1
            random.seed(batch_prng_seed)

            # Generate the batch data
            for _ in range(iterations):
                sample_fixed = 1
                for __ in range(num_segments):
                    if sample_fixed == 1:
                        batch_key = key
                    else:
                        batch_key = [random.randint(0, 255) for _ in range(len(key))]
                    batch_data = [random.randint(0, 255) for _ in range(16)]
                    sample_fixed = random.randint(0, 255) & 0x1

            cipher_gen = AES.new(bytes(batch_key), AES.MODE_ECB)
            expected_result = [x for x in cipher_gen.encrypt(bytes(batch_data))]

            expected_result_json = {
                "ciphertext": expected_result,
                "ciphertext_length": len(expected_result),
            }
            utils.compare_json_data(
                actual_result_json, expected_result_json, ignored_keys_set
            )

    def test_char_aes_batch_random(self):
        for num_segments in num_segments_list:
            masking = True
            key = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
            actual_result = sca_aes_functions.char_aes_batch_random(
                target, iterations, num_segments, fpga, masking, key
            )
            actual_result_json = json.loads(actual_result)

            # Set the synchronized randomness
            batch_prng_seed = 1
            random.seed(batch_prng_seed)

            # Generate the batch data
            for _ in range(iterations):
                for __ in range(num_segments):
                    batch_data = [random.randint(0, 255) for _ in range(16)]

            cipher_gen = AES.new(bytes(key), AES.MODE_ECB)
            expected_result = [x for x in cipher_gen.encrypt(bytes(batch_data))]

            expected_result_json = {
                "ciphertext": expected_result,
                "ciphertext_length": len(expected_result),
            }
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
