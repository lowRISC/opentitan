# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from sw.host.penetrationtests.python.fi.host_scripts import fi_sym_cryptolib_functions
from sw.host.penetrationtests.python.fi.communication.fi_sym_cryptolib_commands import (
    OTFISymCrypto,
)
from python.runfiles import Runfiles
from sw.host.penetrationtests.python.util import targets
from sw.host.penetrationtests.python.util import utils
from sw.host.penetrationtests.python.util import common_library
import json
import unittest
import argparse
import sys
import random
from Crypto.Hash import SHA256, HMAC
from Crypto.Cipher import AES

ignored_keys_set = set([])
opentitantool_path = ""
iterations = 3
repetitions = 3

target = None

# Read in the extra arguments from the opentitan_test.
parser = argparse.ArgumentParser()
parser.add_argument("--bitstream", type=str)
parser.add_argument("--bootstrap", type=str)

args, config_args = parser.parse_known_args()

BITSTREAM = args.bitstream
BOOTSTRAP = args.bootstrap


class SymCryptolibFiTest(unittest.TestCase):
    def test_init(self):
        symfi = OTFISymCrypto(target)
        (
            device_id,
            sensors,
            alerts,
            owner_page,
            boot_log,
            boot_measurements,
            version,
            cryptolib_version,
        ) = symfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
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

        self.assertIn("CRYPTO", cryptolib_version)

    def test_char_aes(self):
        for _ in range(repetitions):
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

            actual_result = fi_sym_cryptolib_functions.char_aes(
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
            )
            actual_result_json = json.loads(actual_result)

            cipher_gen = AES.new(bytes(key), AES.MODE_ECB)
            expected_result = utils.pad_with_zeros([x for x in cipher_gen.encrypt(bytes(data))], 64)
            expected_result_json = {
                "status": 0,
                "data": expected_result,
                "data_len": data_len,
                "cfg": 0,
            }

            utils.compare_json_data(actual_result_json, expected_result_json, ignored_keys_set)

    def test_char_gcm(self):
        for _ in range(repetitions):
            # For testing, we just take a multiple of the block size
            data_len = random.randint(1, 3)
            data_len *= 16
            data = [random.randint(0, 255) for _ in range(data_len)]
            aad_len = random.randint(1, 3)
            aad_len *= 16
            aad = [random.randint(0, 255) for _ in range(aad_len)]
            tag_len = 16
            tag = [0 for _ in range(tag_len)]
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

            actual_result = fi_sym_cryptolib_functions.char_gcm(
                target,
                iterations,
                data,
                data_len,
                key,
                key_len,
                aad,
                aad_len,
                tag,
                tag_len,
                iv,
                cfg,
                trigger,
            )
            actual_result_json = json.loads(actual_result)

            cipher_gen = AES.new(bytes(key), AES.MODE_GCM, bytes(iv))
            cipher_gen.update(bytes(aad))
            expected_ciphertext, expected_tag = cipher_gen.encrypt_and_digest(bytes(data))
            expected_ciphertext = utils.pad_with_zeros([x for x in expected_ciphertext], 64)
            expected_tag = utils.pad_with_zeros([x for x in expected_tag], 64)
            expected_result_json = {
                "status": 0,
                "data": expected_ciphertext,
                "data_len": data_len,
                "tag": expected_tag,
                "tag_len": 16,
                "cfg": 0,
            }

            utils.compare_json_data(actual_result_json, expected_result_json, ignored_keys_set)

    def test_char_hmac(self):
        for _ in range(repetitions):
            data_len = 32
            data = [random.randint(0, 255) for _ in range(data_len)]
            # We only test SHA256
            key_len = 32
            key = [random.randint(0, 255) for _ in range(key_len)]
            cfg = 0
            trigger = 0

            # We just test the first padding mode and the first mode (HMAC)
            padding = 0
            mode = 0

            actual_result = fi_sym_cryptolib_functions.char_hmac(
                target,
                iterations,
                data,
                data_len,
                key,
                key_len,
                padding,
                mode,
                cfg,
                trigger,
            )
            actual_result_json = json.loads(actual_result)

            sha256 = HMAC.new(key=bytes(key), digestmod=SHA256)
            sha256.update(bytes(data))
            expected_result = [x for x in sha256.digest()]
            # Pad the rest with zero
            expected_result = utils.pad_with_zeros([x for x in expected_result], 64)
            expected_result_json = {
                "status": 0,
                "data": expected_result,
                "data_len": 32,
                "cfg": 0,
            }

            utils.compare_json_data(actual_result_json, expected_result_json, ignored_keys_set)

    def test_char_drbg(self):
        entropy_len = 32
        entropy = [random.randint(0, 255) for _ in range(entropy_len)]
        nonce_len = 16
        nonce = [random.randint(0, 255) for _ in range(nonce_len)]
        reseed_interval = 100
        data_len = 16
        mode = 0
        trigger = 1
        cfg = 0

        actual_result = fi_sym_cryptolib_functions.char_drbg(
            target,
            iterations,
            entropy,
            entropy_len,
            nonce,
            nonce_len,
            reseed_interval,
            data_len,
            mode,
            cfg,
            trigger,
        )
        actual_result_json = json.loads(actual_result)

        expected_result_json = {
            "status": 0,
            "cfg": 0,
        }

        drbg_ignored_key_sets = ignored_keys_set.copy()
        drbg_ignored_key_sets.add("data")

        utils.compare_json_data(actual_result_json, expected_result_json, drbg_ignored_key_sets)

    def test_char_trng(self):
        mode = 0
        trigger = 1
        cfg = 0

        actual_result = fi_sym_cryptolib_functions.char_trng(target, iterations, mode, cfg, trigger)
        actual_result_json = json.loads(actual_result)

        expected_result_json = {
            "status": 0,
            "cfg": 0,
        }

        trng_ignored_key_sets = ignored_keys_set.copy()
        trng_ignored_key_sets.add("data")

        utils.compare_json_data(actual_result_json, expected_result_json, trng_ignored_key_sets)


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
