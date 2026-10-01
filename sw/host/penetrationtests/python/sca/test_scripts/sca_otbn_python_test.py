# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from sw.host.penetrationtests.python.sca.host_scripts import sca_otbn_functions
from sw.host.penetrationtests.python.sca.communication.sca_otbn_commands import OTOTBN
from python.runfiles import Runfiles
from sw.host.penetrationtests.python.util import targets
from sw.host.penetrationtests.python.util import utils
import hashlib
import hmac
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
parser.add_argument("--rom", type=str)
parser.add_argument("--otp", type=str)
parser.add_argument("--bootstrap", type=str)

args, config_args = parser.parse_known_args()

BITSTREAM = args.bitstream
ROM_VMEM = args.rom
OTP_VMEM = args.otp
BOOTSTRAP = args.bootstrap


class OtbnScaTest(unittest.TestCase):

    def test_init(self):
        otbnsca = OTOTBN(target)
        device_id, owner_page, boot_log, boot_measurements, version = otbnsca.init()
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
            trigger = 3
            fixed_data1 = 0
            fixed_data2 = 0
            print_flag = True
            actual_result = sca_otbn_functions.char_combi_operations_batch(
                target,
                iterations,
                num_segments,
                fixed_data1,
                fixed_data2,
                print_flag,
                trigger,
            )
            actual_result_json = json.loads(actual_result)

            # Calculate the expected result
            fixed_data_array1 = [fixed_data1 for _ in range(8)]
            fixed_data_array2 = [fixed_data2 for _ in range(8)]
            add = utils.int_to_array(
                (utils.array_to_int(fixed_data_array1) + utils.array_to_int(fixed_data_array2))
                % (1 << 256)
            )
            sub = utils.int_to_array(
                (utils.array_to_int(fixed_data_array1) - utils.array_to_int(fixed_data_array2))
                % (1 << 256)
            )
            xor = utils.int_to_array(
                (utils.array_to_int(fixed_data_array1) ^ utils.array_to_int(fixed_data_array2))
                % (1 << 256)
            )
            shift = utils.int_to_array((utils.array_to_int(fixed_data_array1) << 1) % (1 << 256))
            fixed_data_array1 = [fixed_data1, fixed_data1, 0, 0, 0, 0, 0, 0]
            fixed_data_array2 = [fixed_data2, fixed_data2, 0, 0, 0, 0, 0, 0]
            mult = utils.int_to_array(
                (utils.array_to_int(fixed_data_array1) * utils.array_to_int(fixed_data_array2))
                % (1 << 256)
            )
            FG = 0
            if fixed_data1 == fixed_data2:
                FG += 8
            if fixed_data1 < fixed_data2:
                FG += 1
            if sub[0] & 0x1:
                FG += 4
            if (utils.array_to_int(sub) >> 255) & 0x1:
                FG += 2

            expected_result_json = {
                "result1": [
                    fixed_data1,
                    fixed_data1,
                    fixed_data1,
                    fixed_data1,
                    fixed_data1,
                    fixed_data1,
                    fixed_data1,
                    fixed_data1,
                ],
                "result2": [
                    fixed_data1,
                    fixed_data1,
                    fixed_data1,
                    fixed_data1,
                    fixed_data1,
                    fixed_data1,
                    fixed_data1,
                    fixed_data1,
                ],
                "result3": add,
                "result4": sub,
                "result5": xor,
                "result6": shift,
                "result7": mult,
                "result8": FG,
            }
            utils.compare_json_data(
                actual_result_json, expected_result_json, ignored_keys_set
            )

            fixed_data1 = 1
            fixed_data2 = 1
            print_flag = True
            actual_result = sca_otbn_functions.char_combi_operations_batch(
                target,
                iterations,
                num_segments,
                fixed_data1,
                fixed_data2,
                print_flag,
                trigger,
            )
            actual_result_json = json.loads(actual_result)

            # Calculate the expected result
            fixed_data_array1 = [fixed_data1 for _ in range(8)]
            fixed_data_array2 = [fixed_data2 for _ in range(8)]
            add = utils.int_to_array(
                (utils.array_to_int(fixed_data_array1) + utils.array_to_int(fixed_data_array2))
                % (1 << 256)
            )
            sub = utils.int_to_array(
                (utils.array_to_int(fixed_data_array1) - utils.array_to_int(fixed_data_array2))
                % (1 << 256)
            )
            xor = utils.int_to_array(
                (utils.array_to_int(fixed_data_array1) ^ utils.array_to_int(fixed_data_array2))
                % (1 << 256)
            )
            shift = utils.int_to_array((utils.array_to_int(fixed_data_array1) << 1) % (1 << 256))
            fixed_data_array1 = [fixed_data1, fixed_data1, 0, 0, 0, 0, 0, 0]
            fixed_data_array2 = [fixed_data2, fixed_data2, 0, 0, 0, 0, 0, 0]
            mult = utils.int_to_array(
                (utils.array_to_int(fixed_data_array1) * utils.array_to_int(fixed_data_array2))
                % (1 << 256)
            )
            FG = 0
            if fixed_data1 == fixed_data2:
                FG += 8
            if fixed_data1 < fixed_data2:
                FG += 1
            if sub[0] & 0x1:
                FG += 4
            if (utils.array_to_int(sub) >> 255) & 0x1:
                FG += 2

            expected_result_json = {
                "result1": [
                    fixed_data1,
                    fixed_data1,
                    fixed_data1,
                    fixed_data1,
                    fixed_data1,
                    fixed_data1,
                    fixed_data1,
                    fixed_data1,
                ],
                "result2": [
                    fixed_data1,
                    fixed_data1,
                    fixed_data1,
                    fixed_data1,
                    fixed_data1,
                    fixed_data1,
                    fixed_data1,
                    fixed_data1,
                ],
                "result3": add,
                "result4": sub,
                "result5": xor,
                "result6": shift,
                "result7": mult,
                "result8": FG,
            }
            utils.compare_json_data(
                actual_result_json, expected_result_json, ignored_keys_set
            )

            fixed_data1 = random.getrandbits(32)
            fixed_data2 = random.getrandbits(32)
            print_flag = True
            actual_result = sca_otbn_functions.char_combi_operations_batch(
                target,
                iterations,
                num_segments,
                fixed_data1,
                fixed_data2,
                print_flag,
                trigger,
            )
            actual_result_json = json.loads(actual_result)

            # Calculate the expected result
            fixed_data_array1 = [fixed_data1 for _ in range(8)]
            fixed_data_array2 = [fixed_data2 for _ in range(8)]
            add = utils.int_to_array(
                (utils.array_to_int(fixed_data_array1) + utils.array_to_int(fixed_data_array2))
                % (1 << 256)
            )
            sub = utils.int_to_array(
                (utils.array_to_int(fixed_data_array1) - utils.array_to_int(fixed_data_array2))
                % (1 << 256)
            )
            xor = utils.int_to_array(
                (utils.array_to_int(fixed_data_array1) ^ utils.array_to_int(fixed_data_array2))
                % (1 << 256)
            )
            shift = utils.int_to_array((utils.array_to_int(fixed_data_array1) << 1) % (1 << 256))
            fixed_data_array1 = [fixed_data1, fixed_data1, 0, 0, 0, 0, 0, 0]
            fixed_data_array2 = [fixed_data2, fixed_data2, 0, 0, 0, 0, 0, 0]
            mult = utils.int_to_array(
                (utils.array_to_int(fixed_data_array1) * utils.array_to_int(fixed_data_array2))
                % (1 << 256)
            )
            FG = 0
            if fixed_data1 == fixed_data2:
                FG += 8
            if fixed_data1 < fixed_data2:
                FG += 1
            if sub[0] & 0x1:
                FG += 4
            if (utils.array_to_int(sub) >> 255) & 0x1:
                FG += 2

            expected_result_json = {
                "result1": [
                    fixed_data1,
                    fixed_data1,
                    fixed_data1,
                    fixed_data1,
                    fixed_data1,
                    fixed_data1,
                    fixed_data1,
                    fixed_data1,
                ],
                "result2": [
                    fixed_data1,
                    fixed_data1,
                    fixed_data1,
                    fixed_data1,
                    fixed_data1,
                    fixed_data1,
                    fixed_data1,
                    fixed_data1,
                ],
                "result3": add,
                "result4": sub,
                "result5": xor,
                "result6": shift,
                "result7": mult,
                "result8": FG,
            }
            utils.compare_json_data(
                actual_result_json, expected_result_json, ignored_keys_set
            )

    def test_sha2_otbn(self):
        test_msg = list(b"abc" + b"\x00" * 61)
        msg_len = 3
        modes = [
            (0, hashlib.sha256, 32),
            (1, hashlib.sha384, 48),
            (2, hashlib.sha512, 64),
        ]
        for mode, hash_fn, digest_len in modes:
            expected_digest = list(hash_fn(bytes(test_msg[:msg_len])).digest())
            for en_masks in [False, True]:
                resp = sca_otbn_functions.sha2_single(
                    target, test_msg, msg_len, mode=mode, en_masks=en_masks
                )
                resp_json = json.loads(resp)
                self.assertEqual(resp_json["digest"][:digest_len], expected_digest)

        resp_fvsr = sca_otbn_functions.sha2_batch_fvsr(
            target, 1, 4, test_msg, msg_len, mode=0, en_masks=True
        )
        self.assertIn("digest", json.loads(resp_fvsr))

        resp_rand = sca_otbn_functions.sha2_batch_random(
            target, 1, 4, msg_len, mode=0, en_masks=True
        )
        self.assertIn("digest", json.loads(resp_rand))

    def test_hkdf_otbn(self):
        ikm_bytes = bytes([0x0B] * 22)
        salt_bytes = bytes(range(0x00, 0x0D))
        info_bytes = bytes(range(0xF0, 0xFA))

        ikm = list(ikm_bytes) + [0] * (64 - len(ikm_bytes))
        salt = list(salt_bytes) + [0] * (64 - len(salt_bytes))
        info = list(info_bytes) + [0] * (64 - len(info_bytes))

        modes = [
            (0, hashlib.sha256, 32),
            (1, hashlib.sha384, 48),
            (2, hashlib.sha512, 64),
        ]
        for mode, hash_fn, digest_len in modes:
            expected_prk = hmac.new(salt_bytes, ikm_bytes, hash_fn).digest()
            expected_okm = hmac.new(
                expected_prk, info_bytes + b"\x01", hash_fn
            ).digest()
            for en_masks in [False, True]:
                resp = sca_otbn_functions.hkdf_single(
                    target,
                    ikm,
                    len(ikm_bytes),
                    salt,
                    len(salt_bytes),
                    info,
                    len(info_bytes),
                    okm_blocks=1,
                    mode=mode,
                    en_masks=en_masks,
                )
                resp_json = json.loads(resp)
                self.assertEqual(
                    resp_json["prk"][:digest_len], list(expected_prk)
                )
                self.assertEqual(
                    resp_json["okm"][:digest_len], list(expected_okm)
                )

        resp_fvsr = sca_otbn_functions.hkdf_batch_fvsr(
            target,
            1,
            4,
            ikm,
            len(ikm_bytes),
            salt,
            len(salt_bytes),
            info,
            len(info_bytes),
            okm_blocks=1,
            mode=0,
            en_masks=True,
        )
        self.assertIn("okm", json.loads(resp_fvsr))

        resp_rand = sca_otbn_functions.hkdf_batch_random(
            target,
            1,
            4,
            len(ikm_bytes),
            len(salt_bytes),
            info,
            len(info_bytes),
            okm_blocks=1,
            mode=0,
            en_masks=True,
        )
        self.assertIn("okm", json.loads(resp_rand))


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
    # Load the ROM/OTP memories for FPGAs.
    rom_path = None
    if ROM_VMEM:
        rom_path = r.Rlocation("lowrisc_opentitan/" + ROM_VMEM)
    otp_path = None
    if OTP_VMEM:
        otp_path = r.Rlocation("lowrisc_opentitan/" + OTP_VMEM)
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
        rom_vmem=rom_path,
        otp_vmem=otp_path,
        tool_args=config_args
    )

    target = targets.Target(target_cfg)

    target.initialize_target()

    unittest.main(argv=[sys.argv[0]])
