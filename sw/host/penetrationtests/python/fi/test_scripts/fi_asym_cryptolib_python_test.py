# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from sw.host.penetrationtests.python.fi.host_scripts import fi_asym_cryptolib_functions
from sw.host.penetrationtests.python.fi.communication.fi_asym_cryptolib_commands import (
    OTFIAsymCrypto,
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
from Crypto.PublicKey import RSA, ECC
from Crypto.Signature import pkcs1_15, DSS
from Crypto.Hash import SHA256, SHA384

ignored_keys_set = set([])
opentitantool_path = ""
iterations = 1
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
        asymfi = OTFIAsymCrypto(target)
        (
            device_id,
            sensors,
            alerts,
            owner_page,
            boot_log,
            boot_measurements,
            version,
            cryptolib_version,
        ) = asymfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
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

        self.assertEqual(
            expected_sensors_keys, actual_sensors_keys, "sensor keys do not match"
        )

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

        self.assertEqual(
            expected_alerts_keys, actual_alerts_keys, "alert keys do not match"
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

        self.assertIn("CRYPTO", cryptolib_version)

    def test_char_rsa_encrypt(self):
        n_len = 256
        key = RSA.generate(2048)
        e = key.e
        d = [x for x in (key.d).to_bytes(256, "little")]
        n = [x for x in (key.n).to_bytes(256, "little")]
        data_len = 13
        data = [random.randint(0, 255) for _ in range(data_len)]
        op_enc = True
        cfg = 0
        trigger = 0
        hashing = 0
        padding = 0
        mode = 0

        actual_result = fi_asym_cryptolib_functions.char_rsa_encrypt(
            target,
            iterations,
            data,
            data_len,
            e,
            n,
            n_len,
            d,
            padding,
            hashing,
            mode,
            op_enc,
            cfg,
            trigger,
        )
        actual_result_json = json.loads(actual_result)

        enc_ignored_keys_set = ignored_keys_set.copy()
        enc_ignored_keys_set.add("data")
        enc_ignored_keys_set.add("data_len")

        expected_result_json = {
            "status": 0,
            "d": utils.pad_with_zeros(d, 512),
            "n": utils.pad_with_zeros(n, 512),
            "n_len": 256,
            "err_status": 0,
            "alerts": [0, 0, 0],
            "loc_alerts": 0,
            "ast_alerts": [0, 0],
            "cfg": 0,
        }

        utils.compare_json_data(
            actual_result_json, expected_result_json, enc_ignored_keys_set
        )

        encrypted_data = actual_result_json["data"]
        encrypted_data_len = actual_result_json["data_len"]
        op_enc = False

        actual_result = fi_asym_cryptolib_functions.char_rsa_encrypt(
            target,
            iterations,
            encrypted_data,
            encrypted_data_len,
            e,
            n,
            n_len,
            d,
            padding,
            hashing,
            mode,
            op_enc,
            cfg,
            trigger,
        )
        actual_result_json = json.loads(actual_result)

        decrypted_data = actual_result_json["data"]
        decrypted_data_len = actual_result_json["data_len"]

        assert decrypted_data_len == data_len, f"{decrypted_data_len} vs. {data_len}"
        assert decrypted_data[:data_len] == data, f"{decrypted_data} vs. {data}"

    def test_char_rsa_sign(self):
        n_len = 256
        key = RSA.generate(2048)
        e = key.e
        d = [x for x in (key.d).to_bytes(256, "little")]
        n = [x for x in (key.n).to_bytes(256, "little")]
        data_len = 13
        data = [random.randint(0, 255) for _ in range(data_len)]
        cfg = 0
        trigger = 0
        hashing = 0
        padding = 0

        actual_result = fi_asym_cryptolib_functions.char_rsa_sign(
            target,
            iterations,
            data,
            data_len,
            e,
            n,
            n_len,
            d,
            padding,
            hashing,
            cfg,
            trigger,
        )
        actual_result_json = json.loads(actual_result)

        sign_ignored_keys_set = ignored_keys_set.copy()
        sign_ignored_keys_set.add("sig")

        expected_result_json = {
            "status": 0,
            "d": utils.pad_with_zeros(d, 512),
            "n": utils.pad_with_zeros(n, 512),
            "n_len": 256,
            "sig_len": 256,
            "err_status": 0,
            "alerts": [0, 0, 0],
            "loc_alerts": 0,
            "ast_alerts": [0, 0],
            "cfg": 0,
        }

        utils.compare_json_data(
            actual_result_json, expected_result_json, sign_ignored_keys_set
        )

        signature = actual_result_json["sig"]
        signature = signature[:256]
        signature.reverse()
        h_verified = SHA256.new(bytes(data))
        verifier = pkcs1_15.new(key.public_key())
        verifier.verify(h_verified, bytes(signature))

    def test_char_rsa_verify(self):
        key = RSA.generate(2048)
        e = key.e
        n = [x for x in (key.n).to_bytes(256, "little")]
        n_len = 256
        data_len = 13
        data = [random.randint(0, 255) for _ in range(data_len)]
        h = SHA256.new(bytes(data))
        signer = pkcs1_15.new(key)
        signature = signer.sign(h)
        sig = [x for x in signature]
        sig.reverse()
        sig_len = len(sig)
        cfg = 0
        trigger = 0
        hashing = 0
        padding = 0

        actual_result = fi_asym_cryptolib_functions.char_rsa_verify(
            target,
            iterations,
            data,
            data_len,
            e,
            n,
            n_len,
            sig,
            sig_len,
            padding,
            hashing,
            cfg,
            trigger,
        )
        actual_result_json = json.loads(actual_result)

        expected_result_json = {
            "status": 0,
            "result": True,
            "err_status": 0,
            "alerts": [0, 0, 0],
            "loc_alerts": 0,
            "ast_alerts": [0, 0],
            "cfg": 0,
        }

        utils.compare_json_data(
            actual_result_json, expected_result_json, ignored_keys_set
        )

    def test_char_p256_ecdh(self):
        private_key = ECC.generate(curve="P-256")
        private_key_array = [x for x in private_key.d.to_bytes(32, "little")]
        key = ECC.generate(curve="P-256")
        public_point = key.pointQ
        public_x = [x for x in public_point.x.to_bytes(32, "little")]
        public_y = [x for x in public_point.y.to_bytes(32, "little")]
        cfg = 0
        trigger = 0

        actual_result = fi_asym_cryptolib_functions.char_p256_ecdh(
            target,
            iterations,
            private_key_array,
            public_x,
            public_y,
            cfg,
            trigger,
        )
        actual_result_json = json.loads(actual_result)

        shared_secret_point = key.pointQ * private_key.d
        shared_secret_point = [x for x in shared_secret_point.x.to_bytes(32, "little")]

        expected_result_json = {
            "status": 0,
            "shared_key": shared_secret_point,
            "err_status": 0,
            "alerts": [0, 0, 0],
            "loc_alerts": 0,
            "ast_alerts": [0, 0],
            "cfg": 0,
        }

        utils.compare_json_data(
            actual_result_json, expected_result_json, ignored_keys_set
        )

    def test_char_p256_sign(self):
        key = ECC.generate(curve="P-256")
        scalar = [x for x in key.d.to_bytes(32, "little")]
        pubx = [x for x in key.pointQ.x.to_bytes(32, "little")]
        puby = [x for x in key.pointQ.y.to_bytes(32, "little")]
        message = [random.randint(0, 255) for _ in range(16)]
        h = SHA256.new(bytes(message))
        message_digest = [x for x in h.digest()]
        cfg = 0
        trigger = 0

        actual_result = fi_asym_cryptolib_functions.char_p256_sign(
            target,
            iterations,
            scalar,
            pubx,
            puby,
            message_digest,
            cfg,
            trigger,
        )
        actual_result_json = json.loads(actual_result)

        sign_ignored_keys_set = ignored_keys_set.copy()
        sign_ignored_keys_set.add("r")
        sign_ignored_keys_set.add("s")
        sign_ignored_keys_set.add("pubx")
        sign_ignored_keys_set.add("puby")

        expected_result_json = {
            "status": 0,
            "err_status": 0,
            "alerts": [0, 0, 0],
            "loc_alerts": 0,
            "ast_alerts": [0, 0],
            "cfg": 0,
        }

        utils.compare_json_data(
            actual_result_json, expected_result_json, sign_ignored_keys_set
        )

        verifier = DSS.new(key.public_key(), "fips-186-3")
        r = actual_result_json["r"]
        s = actual_result_json["s"]
        r.reverse()
        s.reverse()
        signature = r + s
        verifier.verify(h, bytes(signature))

    def test_char_p256_verify(self):
        key = ECC.generate(curve="P-256")
        pubx = [x for x in key.pointQ.x.to_bytes(32, "little")]
        puby = [x for x in key.pointQ.y.to_bytes(32, "little")]

        message = [random.randint(0, 255) for _ in range(16)]
        h = SHA256.new(bytes(message))

        signer = DSS.new(key, "fips-186-3")
        signature = [x for x in signer.sign(h)]
        r_bytes = signature[:32]
        s_bytes = signature[32:]
        r_bytes.reverse()
        s_bytes.reverse()
        cfg = 0
        trigger = 1

        h = SHA256.new(bytes(message))
        message_digest = [x for x in h.digest()]

        actual_result = fi_asym_cryptolib_functions.char_p256_verify(
            target,
            iterations,
            pubx,
            puby,
            r_bytes,
            s_bytes,
            message_digest,
            cfg,
            trigger,
        )
        actual_result_json = json.loads(actual_result)

        expected_result_json = {
            "status": 0,
            "result": True,
            "err_status": 0,
            "alerts": [0, 0, 0],
            "loc_alerts": 0,
            "ast_alerts": [0, 0],
            "cfg": 0,
        }

        utils.compare_json_data(
            actual_result_json, expected_result_json, ignored_keys_set
        )

    def test_char_p384_ecdh(self):
        private_key = ECC.generate(curve="P-384")
        private_key_array = [x for x in private_key.d.to_bytes(48, "little")]
        key = ECC.generate(curve="P-384")
        public_point = key.pointQ
        public_x = [x for x in public_point.x.to_bytes(48, "little")]
        public_y = [x for x in public_point.y.to_bytes(48, "little")]
        cfg = 0
        trigger = 0

        actual_result = fi_asym_cryptolib_functions.char_p384_ecdh(
            target,
            iterations,
            private_key_array,
            public_x,
            public_y,
            cfg,
            trigger,
        )
        actual_result_json = json.loads(actual_result)

        shared_secret_point = key.pointQ * private_key.d
        shared_secret_point = [x for x in shared_secret_point.x.to_bytes(48, "little")]

        expected_result_json = {
            "status": 0,
            "shared_key": shared_secret_point,
            "err_status": 0,
            "alerts": [0, 0, 0],
            "loc_alerts": 0,
            "ast_alerts": [0, 0],
            "cfg": 0,
        }

        utils.compare_json_data(
            actual_result_json, expected_result_json, ignored_keys_set
        )

    def test_char_p384_sign(self):
        key = ECC.generate(curve="P-384")
        scalar = [x for x in key.d.to_bytes(48, "little")]
        pubx = [x for x in key.pointQ.x.to_bytes(48, "little")]
        puby = [x for x in key.pointQ.y.to_bytes(48, "little")]
        message = [random.randint(0, 255) for _ in range(16)]
        h = SHA384.new(bytes(message))
        message_digest = [x for x in h.digest()]
        cfg = 0
        trigger = 0

        actual_result = fi_asym_cryptolib_functions.char_p384_sign(
            target,
            iterations,
            scalar,
            pubx,
            puby,
            message_digest,
            cfg,
            trigger,
        )
        actual_result_json = json.loads(actual_result)

        sign_ignored_keys_set = ignored_keys_set.copy()
        sign_ignored_keys_set.add("r")
        sign_ignored_keys_set.add("s")
        sign_ignored_keys_set.add("pubx")
        sign_ignored_keys_set.add("puby")

        expected_result_json = {
            "status": 0,
            "err_status": 0,
            "alerts": [0, 0, 0],
            "loc_alerts": 0,
            "ast_alerts": [0, 0],
            "cfg": 0,
        }

        utils.compare_json_data(
            actual_result_json, expected_result_json, sign_ignored_keys_set
        )

        verifier = DSS.new(key.public_key(), "fips-186-3")
        r = actual_result_json["r"]
        s = actual_result_json["s"]
        r.reverse()
        s.reverse()
        signature = r + s
        verifier.verify(h, bytes(signature))

    def test_char_p384_verify(self):
        key = ECC.generate(curve="P-384")
        pubx = [x for x in key.pointQ.x.to_bytes(48, "little")]
        puby = [x for x in key.pointQ.y.to_bytes(48, "little")]

        message = [random.randint(0, 255) for _ in range(16)]
        h = SHA384.new(bytes(message))

        signer = DSS.new(key, "fips-186-3")
        signature = [x for x in signer.sign(h)]
        r_bytes = signature[:48]
        s_bytes = signature[48:]
        r_bytes.reverse()
        s_bytes.reverse()
        cfg = 0
        trigger = 1

        h = SHA384.new(bytes(message))
        message_digest = [x for x in h.digest()]

        actual_result = fi_asym_cryptolib_functions.char_p384_verify(
            target,
            iterations,
            pubx,
            puby,
            r_bytes,
            s_bytes,
            message_digest,
            cfg,
            trigger,
        )
        actual_result_json = json.loads(actual_result)

        expected_result_json = {
            "status": 0,
            "result": True,
            "err_status": 0,
            "alerts": [0, 0, 0],
            "loc_alerts": 0,
            "ast_alerts": [0, 0],
            "cfg": 0,
        }

        utils.compare_json_data(
            actual_result_json, expected_result_json, ignored_keys_set
        )

    def test_char_ed25519_sign(self):
        scalar = [random.randint(0, 255) for _ in range(32)]
        message = [random.randint(0, 255) for _ in range(16)]
        message_padded = utils.pad_with_zeros(message, 128)
        message_len = len(message)
        cfg = 0
        trigger = 1

        actual_result = fi_asym_cryptolib_functions.char_ed25519_sign(
            target,
            iterations,
            scalar,
            message_padded,
            message_len,
            cfg,
            trigger,
        )
        actual_result_json = json.loads(actual_result)

        sign_ignored_keys_set = ignored_keys_set.copy()
        sign_ignored_keys_set.add("r")
        sign_ignored_keys_set.add("s")
        sign_ignored_keys_set.add("pubx")
        sign_ignored_keys_set.add("puby")

        expected_result_json = {
            "status": 0,
            "err_status": 0,
            "alerts": [0, 0, 0],
            "loc_alerts": 0,
            "ast_alerts": [0, 0],
            "cfg": 0,
        }
        # As the verify is done on the device after the sign, just check if the reported
        # status is valid.
        utils.compare_json_data(
            actual_result_json, expected_result_json, sign_ignored_keys_set
        )

    def test_char_ed25519_verify(self):
        scalar = [random.randint(0, 255) for _ in range(32)]
        message = [random.randint(0, 255) for _ in range(16)]
        message_padded = utils.pad_with_zeros(message, 128)
        message_len = len(message)
        cfg = 0
        trigger = 1

        # Sign on device to obtain a valid signature and public key.
        sign_result = fi_asym_cryptolib_functions.char_ed25519_sign(
            target,
            iterations,
            scalar,
            message_padded,
            message_len,
            cfg,
            trigger,
        )
        sign_result_json = json.loads(sign_result)

        pubx = sign_result_json["pubx"]
        puby = [0] * 32
        r = sign_result_json["r"]
        s = sign_result_json["s"]

        actual_result = fi_asym_cryptolib_functions.char_ed25519_verify(
            target,
            iterations,
            pubx,
            puby,
            r,
            s,
            message_padded,
            message_len,
            cfg,
            trigger,
        )
        actual_result_json = json.loads(actual_result)

        expected_result_json = {
            "status": 0,
            "result": True,
            "err_status": 0,
            "alerts": [0, 0, 0],
            "loc_alerts": 0,
            "ast_alerts": [0, 0],
            "cfg": 0,
        }

        utils.compare_json_data(
            actual_result_json, expected_result_json, ignored_keys_set
        )

    def test_char_x25519_base_mult(self):
        # Test vector from RFC 7748, Section 6.1
        # https://datatracker.ietf.org/doc/html/rfc7748#section-6.1
        # Alice's Private Key
        private_key_bytes = bytes.fromhex(
            "77076d0a7318a57d3c16c17251b26645df4c2f87ebc0992ab177fba51db92c2a"
        )
        scalar = list(private_key_bytes)
        cfg = 0
        trigger = 0

        actual_result = fi_asym_cryptolib_functions.char_x25519_base_mult(
            target, iterations, scalar, cfg, trigger
        )
        actual_result_json = json.loads(actual_result)

        # Alice's Public Key
        expected_public = list(
            bytes.fromhex(
                "8520f0098930a754748b7ddcb43ef75a0dbf3a0d26381af4eba4a98eaa9b4e6a"
            )
        )

        expected_result_json = {
            "status": 0,
            "x": expected_public,
            "y": [0] * 32,  # X25519 has no Y coordinate
            "err_status": 0,
            "alerts": [0, 0, 0],
            "loc_alerts": 0,
            "ast_alerts": [0, 0],
            "cfg": 0,
        }
        utils.compare_json_data(
            actual_result_json, expected_result_json, ignored_keys_set
        )

    def test_char_x25519_ecdh(self):
        # Test vector from RFC 7748, Section 6.1
        # https://datatracker.ietf.org/doc/html/rfc7748#section-6.1
        # Alice's Private Key
        private_key_bytes = bytes.fromhex(
            "77076d0a7318a57d3c16c17251b26645df4c2f87ebc0992ab177fba51db92c2a"
        )
        private_key = list(private_key_bytes)

        # Bob's Public Key
        public_bob_bytes = bytes.fromhex(
            "de9edb7d7b7dc1b4d35b61c2ece435373f8343c85b78674dadfc7e146f882b4f"
        )
        public_x = list(public_bob_bytes)
        public_y = [0] * 32  # X25519 uses the u-coordinate (x) exclusively
        cfg = 0
        trigger = 0

        actual_result = fi_asym_cryptolib_functions.char_x25519_ecdh(
            target, iterations, private_key, public_x, public_y, cfg, trigger
        )
        actual_result_json = json.loads(actual_result)

        expected_shared = list(
            bytes.fromhex(
                "4a5d9d5ba4ce2de1728e3bf480350f25e07e21c947d19e3376f09b3c1e161742"
            )
        )

        expected_result_json = {
            "status": 0,
            "shared_key": expected_shared,
            "err_status": 0,
            "alerts": [0, 0, 0],
            "loc_alerts": 0,
            "ast_alerts": [0, 0],
            "cfg": 0,
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
