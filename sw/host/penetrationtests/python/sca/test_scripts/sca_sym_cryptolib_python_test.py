# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from sw.host.penetrationtests.python.sca.host_scripts import sca_sym_cryptolib_functions
from sw.host.penetrationtests.python.sca.communication.sca_sym_cryptolib_commands import (
    OTSymCrypto,
)
from python.runfiles import Runfiles
from sw.host.penetrationtests.python.util import targets
from sw.host.penetrationtests.python.util import utils
import json
import random
import unittest
import argparse
import sys
from Crypto.Hash import SHA256, HMAC
from Crypto.Cipher import AES

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


class SymCryptoScaTest(unittest.TestCase):

    def test_init(self):
        symsca = OTSymCrypto(target)
        device_id, owner_page, boot_log, boot_measurements, version = symsca.init()
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

    def test_char_aes_fvsr_plaintext(self):
        for num_segments in num_segments_list:
            # For testing, we just take a multiple of the block size
            data_len = random.randint(1, 3)
            data_len *= 16
            data = [random.randint(0, 255) for _ in range(data_len)]
            key_len_idx = random.randint(0, 2)
            if key_len_idx == 0:
                key_len = 16
            elif key_len_idx == 1:
                key_len = 24
            else:
                key_len = 32
            key = [random.randint(0, 255) for _ in range(key_len)]
            iv = [random.randint(0, 255) for _ in range(16)]
            op_enc = True
            cfg = 0
            trigger = 0

            # We just test the first padding mode (no padding) and the first mode (ECB)
            padding = 0
            mode = 0

            actual_result = sca_sym_cryptolib_functions.char_aes_fvsr_plaintext(
                target,
                iterations,
                data,
                data_len,
                key,
                key_len,
                iv,
                padding,
                mode,
                op_enc,
                cfg,
                trigger,
                num_segments,
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
                        batch_data = data
                    else:
                        batch_data = [random.randint(0, 255) for _ in range(len(data))]
                    sample_fixed = random.randint(0, 255) & 0x1

            cipher_gen = AES.new(bytes(key), AES.MODE_ECB)
            expected_result = utils.pad_with_zeros(
                [x for x in cipher_gen.encrypt(bytes(batch_data))], 64
            )
            expected_result_json = {
                "status": 0,
                "data": expected_result,
                "data_len": data_len,
                "cfg": 0,
            }

            utils.compare_json_data(
                actual_result_json, expected_result_json, ignored_keys_set
            )

    def test_char_aes_daisy(self):
        for num_segments in num_segments_list:
            # For daisy chaining, you can only take 1 block
            data_len = 16
            data = [random.randint(0, 255) for _ in range(data_len)]
            key_len_idx = random.randint(0, 2)
            if key_len_idx == 0:
                key_len = 16
            elif key_len_idx == 1:
                key_len = 24
            else:
                key_len = 32
            key = [random.randint(0, 255) for _ in range(key_len)]
            iv = [random.randint(0, 255) for _ in range(16)]
            op_enc = True
            cfg = 0
            trigger = 0

            # We just test the first padding mode (no padding) and the first mode (ECB)
            padding = 0
            mode = 0

            actual_result = sca_sym_cryptolib_functions.char_aes_daisy(
                target,
                iterations,
                data,
                data_len,
                key,
                key_len,
                iv,
                padding,
                mode,
                op_enc,
                cfg,
                trigger,
                num_segments,
            )
            actual_result_json = json.loads(actual_result)

            cipher_gen = AES.new(bytes(key), AES.MODE_ECB)
            for _ in range(iterations):
                chained_text = data
                for __ in range(num_segments):
                    chained_text = [x for x in cipher_gen.encrypt(bytes(chained_text))]

            expected_result_json = {
                "status": 0,
                "data": utils.pad_with_zeros(chained_text, 64),
                "data_len": data_len,
                "cfg": 0,
            }

            utils.compare_json_data(
                actual_result_json, expected_result_json, ignored_keys_set
            )

    def test_char_gcm_fvsr_plaintext(self):
        for num_segments in num_segments_list:
            # For testing, we just take a multiple of the block size
            data_len = random.randint(1, 3)
            data_len *= 16
            data = [random.randint(0, 255) for _ in range(data_len)]
            aad_len = random.randint(1, 64)
            aad = [random.randint(0, 255) for _ in range(aad_len)]
            key_len_idx = random.randint(0, 2)
            if key_len_idx == 0:
                key_len = 16
            elif key_len_idx == 1:
                key_len = 24
            else:
                key_len = 32
            key = [random.randint(0, 255) for _ in range(key_len)]
            iv = [random.randint(0, 255) for _ in range(16)]
            cfg = 0
            trigger = 0

            actual_result = sca_sym_cryptolib_functions.char_gcm_fvsr_plaintext(
                target,
                iterations,
                data,
                data_len,
                key,
                key_len,
                aad,
                aad_len,
                iv,
                cfg,
                trigger,
                num_segments,
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
                        batch_data = data
                    else:
                        batch_data = [random.randint(0, 255) for _ in range(len(data))]
                    sample_fixed = random.randint(0, 255) & 0x1

            cipher_gen = AES.new(bytes(key), AES.MODE_GCM, bytes(iv))
            cipher_gen.update(bytes(aad))
            expected_ciphertext, expected_tag = cipher_gen.encrypt_and_digest(
                bytes(batch_data)
            )
            expected_ciphertext = utils.pad_with_zeros(
                [x for x in expected_ciphertext], 64
            )
            expected_tag = utils.pad_with_zeros([x for x in expected_tag], 64)
            expected_result_json = {
                "status": 0,
                "data": expected_ciphertext,
                "data_len": data_len,
                "tag": expected_tag,
                "tag_len": 16,
                "cfg": 0,
            }

            utils.compare_json_data(
                actual_result_json, expected_result_json, ignored_keys_set
            )

    def test_char_gcm_daisy(self):
        for num_segments in num_segments_list:
            # For daisy chaining, we work with 1 block
            data_len = 16
            data = [random.randint(0, 255) for _ in range(data_len)]
            aad_len = random.randint(1, 64)
            aad = [random.randint(0, 255) for _ in range(aad_len)]
            key_len_idx = random.randint(0, 2)
            if key_len_idx == 0:
                key_len = 16
            elif key_len_idx == 1:
                key_len = 24
            else:
                key_len = 32
            key = [random.randint(0, 255) for _ in range(key_len)]
            iv = [random.randint(0, 255) for _ in range(16)]
            cfg = 0
            trigger = 0

            actual_result = sca_sym_cryptolib_functions.char_gcm_daisy(
                target,
                iterations,
                data,
                data_len,
                key,
                key_len,
                aad,
                aad_len,
                iv,
                cfg,
                trigger,
                num_segments,
            )
            actual_result_json = json.loads(actual_result)

            for _ in range(iterations):
                chained_text = data
                for __ in range(num_segments):
                    cipher_gen = AES.new(bytes(key), AES.MODE_GCM, bytes(iv))
                    cipher_gen.update(bytes(aad))
                    ciphertext, tag = cipher_gen.encrypt_and_digest(bytes(chained_text))
                    chained_text = [x for x in ciphertext]

            expected_ciphertext = utils.pad_with_zeros([x for x in chained_text], 64)
            expected_tag = utils.pad_with_zeros([x for x in tag], 64)
            expected_result_json = {
                "status": 0,
                "data": expected_ciphertext,
                "data_len": data_len,
                "tag": expected_tag,
                "tag_len": 16,
                "cfg": 0,
            }

            utils.compare_json_data(
                actual_result_json, expected_result_json, ignored_keys_set
            )

    def test_char_hmac_fvsr_plaintext(self):
        for num_segments in num_segments_list:
            data_len = 32
            data = [random.randint(0, 255) for _ in range(data_len)]
            # We only test SHA256
            key_len = 32
            key = [random.randint(0, 255) for _ in range(key_len)]
            cfg = 0
            trigger = 0

            # We just test the first padding mode and the first hash mode (HMAC)
            hash_mode = 0
            mode = 0

            actual_result = sca_sym_cryptolib_functions.char_hmac_fvsr_plaintext(
                target,
                iterations,
                data,
                data_len,
                key,
                key_len,
                hash_mode,
                mode,
                cfg,
                trigger,
                num_segments,
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
                        batch_data = data
                    else:
                        batch_data = [random.randint(0, 255) for _ in range(len(data))]
                    sample_fixed = random.randint(0, 255) & 0x1

            sha256 = HMAC.new(key=bytes(key), digestmod=SHA256)
            sha256.update(bytes(batch_data))
            expected_result = [x for x in sha256.digest()]
            # Pad the rest with zero
            expected_result = utils.pad_with_zeros([x for x in expected_result], 64)
            expected_result_json = {
                "status": 0,
                "data": expected_result,
                "data_len": 32,
                "cfg": 0,
            }

            utils.compare_json_data(
                actual_result_json, expected_result_json, ignored_keys_set
            )

    def test_char_hmac_daisy(self):
        for num_segments in num_segments_list:
            data_len = 16
            data = [random.randint(0, 255) for _ in range(data_len)]
            # We only test SHA256
            key_len = 32
            key = [random.randint(0, 255) for _ in range(key_len)]
            cfg = 0
            trigger = 0

            # We just test the first padding mode and the first hash mode (HMAC)
            hash_mode = 0
            mode = 0

            actual_result = sca_sym_cryptolib_functions.char_hmac_daisy(
                target,
                iterations,
                data,
                data_len,
                key,
                key_len,
                hash_mode,
                mode,
                cfg,
                trigger,
                num_segments,
            )
            actual_result_json = json.loads(actual_result)

            for _ in range(iterations):
                chained_text = data
                for __ in range(num_segments):
                    chained_text = chained_text[:data_len]
                    sha256 = HMAC.new(key=bytes(key), digestmod=SHA256)
                    sha256.update(bytes(chained_text))
                    chained_text = [x for x in sha256.digest()]

            expected_result = utils.pad_with_zeros([x for x in chained_text], 64)
            expected_result_json = {
                "status": 0,
                "data": expected_result,
                "data_len": 32,
                "cfg": 0,
            }

            utils.compare_json_data(
                actual_result_json, expected_result_json, ignored_keys_set
            )

    def test_char_drbg(self):
        for num_segments in num_segments_list:
            entropy_len = 32
            entropy = [random.randint(0, 255) for _ in range(entropy_len)]
            add_len = 16
            add = [random.randint(0, 255) for _ in range(add_len)]
            reseed_interval = 100
            data_len = 16
            mode = 0
            trigger = 1
            cfg = 0

            actual_result = sca_sym_cryptolib_functions.char_drbg(
                target,
                iterations,
                entropy,
                entropy_len,
                add,
                add_len,
                reseed_interval,
                data_len,
                mode,
                cfg,
                trigger,
                num_segments,
            )
            actual_result_json = json.loads(actual_result)

            expected_result_json = {
                "status": 0,
                "cfg": 0,
            }

            drbg_ignored_key_sets = ignored_keys_set.copy()
            drbg_ignored_key_sets.add("data")

            utils.compare_json_data(
                actual_result_json, expected_result_json, drbg_ignored_key_sets
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
