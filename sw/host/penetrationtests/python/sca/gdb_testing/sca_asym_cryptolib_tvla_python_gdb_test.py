# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import json
import os
import random
import unittest
from Crypto.Cipher import PKCS1_OAEP
from Crypto.Hash import SHA256
from Crypto.PublicKey import ECC, RSA
from python.runfiles import Runfiles
from sw.host.penetrationtests.python.sca.communication.sca_asym_cryptolib_commands import (
    OTAsymCrypto,
)
from sw.host.penetrationtests.python.sca.host_scripts import (
    sca_asym_cryptolib_functions,
)
from sw.host.penetrationtests.python.util import targets
from sw.host.penetrationtests.python.util import utils
from sw.host.penetrationtests.python.util.gdb_tvla import GDBTVLACampaign

target = None
campaign = None

# Evaluate at most MAX_PC_DEPTH occurrences of each PC in a loop (like FI tests).
MAX_PC_DEPTH = 2
# Default total number of TVLA traces per execution (matching OTBN TVLA tests).
NUM_TRACES = 5000
MAX_BATCH_SIZE = 50
DEFAULT_WORKERS = 16 if targets.is_qemu_available() else 1
WORKERS = int(os.environ.get("TVLA_WORKERS", str(DEFAULT_WORKERS)))

# Read in the extra arguments from the opentitan_test.
parser = argparse.ArgumentParser()
parser.add_argument("--bitstream", type=str)
parser.add_argument("--bootstrap", type=str)
parser.add_argument("--num-traces", type=int, default=NUM_TRACES)
parser.add_argument("--max-pc-depth", type=int, default=MAX_PC_DEPTH)
parser.add_argument("--workers", type=int, default=WORKERS)
parser.add_argument("--gdb-port", type=int, default=3333)
utils.add_test_selection_args(parser)

args, config_args = parser.parse_known_args()

BITSTREAM = args.bitstream
BOOTSTRAP = args.bootstrap
NUM_TRACES = args.num_traces
MAX_PC_DEPTH = args.max_pc_depth
WORKERS = (
    max(1, (os.cpu_count() or 2) // 2) if args.workers <= 0 else args.workers
)


class AsymCryptolibScaTvlaGdbTest(unittest.TestCase):

    @classmethod
    def setUpClass(cls):
        if target is None:
            raise RuntimeError("Target failed to initialize.")
        target.initialize_target()
        OTAsymCrypto(target).init()
        cls.rsa_key = RSA.generate(
            2048, randfunc=random.Random(42).randbytes
        )

    def setUp(self):
        if getattr(getattr(target, "target", None), "_faulted", False):
            target.reset_target()
            OTAsymCrypto(target).init()

    @classmethod
    def tearDownClass(cls):
        if campaign is not None:
            campaign.close_gdb()
        if target is not None:
            target.close_openocd()

    @staticmethod
    def _batch_params(total_traces):
        """Split total_traces into (iterations, num_iterations) capped at MAX_BATCH_SIZE."""
        max_batch = MAX_BATCH_SIZE
        if WORKERS > 1:
            max_batch = max(1, min(MAX_BATCH_SIZE, total_traces // WORKERS))
        num_iterations = min(total_traces, max_batch)
        iterations = max(
            1, (total_traces + num_iterations - 1) // num_iterations
        )
        return iterations, num_iterations

    @staticmethod
    def _single_schedule(total_traces):
        """Return an alternating Fixed(0)/Random(1) schedule of length total_traces."""
        return [i % 2 for i in range(total_traces)]

    @staticmethod
    def _fvsr_schedule(iterations, num_iterations, fixed_data):
        """Return (groups, last_batch_data) synchronized with OTPRNG([1, 0, 0, 0])."""
        random.seed(1)
        groups = []
        batch_data = list(fixed_data)
        for _ in range(iterations):
            sample_fixed = 1
            for _ in range(num_iterations):
                if sample_fixed == 1:
                    groups.append(0)
                    batch_data = list(fixed_data)
                else:
                    groups.append(1)
                    batch_data = [
                        random.randint(0, 255) for _ in range(len(fixed_data))
                    ]
                sample_fixed = random.randint(0, 255) & 0x1
        return groups, batch_data

    @staticmethod
    def _x25519_public_key(scalar_bytes):
        """Derive a valid Curve25519 public key (never on the quadratic twist)."""
        p = (1 << 255) - 19
        k_list = bytearray(scalar_bytes)
        k_list[0] &= 248
        k_list[31] &= 127
        k_list[31] |= 64
        k = int.from_bytes(k_list, "little")
        x1 = 9
        x2, z2 = 1, 0
        x3, z3 = x1, 1
        swap = 0
        for t in range(254, -1, -1):
            kt = (k >> t) & 1
            swap ^= kt
            if swap:
                x2, x3 = x3, x2
                z2, z3 = z3, z2
            swap = kt
            a = (x2 + z2) % p
            aa = (a * a) % p
            b = (x2 - z2) % p
            bb = (b * b) % p
            e = (aa - bb) % p
            c = (x3 + z3) % p
            d = (x3 - z3) % p
            da = (d * a) % p
            cb = (c * b) % p
            x3 = pow(da + cb, 2, p)
            z3 = (x1 * pow(da - cb, 2, p)) % p
            x2 = (aa * bb) % p
            z2 = (e * (aa + 121665 * e)) % p
        if swap:
            x2, x3 = x3, x2
            z2, z3 = z3, z2
        res = (x2 * pow(z2, p - 2, p)) % p
        return list(res.to_bytes(32, "little"))

    def test_char_p256_base_mult_fvsr_tvla(self):
        """Hook char_p256_base_mult_fvsr and inspect Ibex RF leakage during P-256 base mult."""
        campaign.reset_stats()
        iterations, num_iterations = self._batch_params(NUM_TRACES)
        private_key = ECC.construct(curve="P-256", d=126792)
        scalar = [x for x in private_key.d.to_bytes(32, "little")]
        cfg = 0
        trigger = 1

        groups, _ = self._fvsr_schedule(iterations, num_iterations, scalar)

        with campaign.hook(target, groups=groups):
            actual_result = sca_asym_cryptolib_functions.char_p256_base_mult_fvsr(
                target,
                iterations,
                scalar,
                cfg,
                trigger,
                num_iterations,
                reset=False,
            )
        actual_result_json = json.loads(actual_result)
        self.assertEqual(actual_result_json["status"], 0)
        print("\n" + campaign.format_report(), flush=True)
        leaks = campaign.get_leaks()
        self.assertGreater(len(campaign.accumulator.sites), 0)
        self.assertEqual(len(leaks), 0)

    def test_char_p384_base_mult_fvsr_tvla(self):
        """Hook char_p384_base_mult_fvsr and inspect Ibex RF leakage during P-384 base mult."""
        campaign.reset_stats()
        iterations, num_iterations = self._batch_params(NUM_TRACES)
        private_key = ECC.construct(curve="P-384", d=34436)
        scalar = [x for x in private_key.d.to_bytes(48, "little")]
        cfg = 0
        trigger = 1

        groups, _ = self._fvsr_schedule(iterations, num_iterations, scalar)

        with campaign.hook(target, groups=groups):
            actual_result = sca_asym_cryptolib_functions.char_p384_base_mult_fvsr(
                target,
                iterations,
                scalar,
                cfg,
                trigger,
                num_iterations,
                reset=False,
            )
        actual_result_json = json.loads(actual_result)
        self.assertEqual(actual_result_json["status"], 0)
        print("\n" + campaign.format_report(), flush=True)
        leaks = campaign.get_leaks()
        self.assertGreater(len(campaign.accumulator.sites), 0)
        self.assertEqual(len(leaks), 0)

    def test_char_x25519_base_mult_fvsr_tvla(self):
        """Hook char_x25519_base_mult_fvsr and inspect Ibex RF leakage during X25519 keygen."""
        campaign.reset_stats()
        iterations, num_iterations = self._batch_params(NUM_TRACES)
        scalar = list((444400).to_bytes(32, "little"))
        cfg = 0
        trigger = 1

        groups, _ = self._fvsr_schedule(iterations, num_iterations, scalar)

        with campaign.hook(target, groups=groups):
            actual_result = sca_asym_cryptolib_functions.char_x25519_base_mult_fvsr(
                target,
                iterations,
                scalar,
                cfg,
                trigger,
                num_iterations,
                reset=False,
            )
        actual_result_json = json.loads(actual_result)
        self.assertEqual(actual_result_json["status"], 0)
        print("\n" + campaign.format_report(), flush=True)
        leaks = campaign.get_leaks()
        self.assertGreater(len(campaign.accumulator.sites), 0)
        self.assertEqual(len(leaks), 0)

    def test_char_p256_ecdh_tvla(self):
        """Run Fixed-vs-Random TVLA on cryptolib P-256 ECDH public key handling."""
        campaign.reset_stats()
        asymsca = OTAsymCrypto(target)
        asymsca.init()

        rng = random.Random(42)
        private_key = ECC.construct(curve="P-256", d=2)
        private_key_array = [x for x in private_key.d.to_bytes(32, "little")]
        fixed_pub = ECC.construct(curve="P-256", d=9856).pointQ
        fixed_x = [x for x in fixed_pub.x.to_bytes(32, "little")]
        fixed_y = [x for x in fixed_pub.y.to_bytes(32, "little")]
        cfg = 0
        trigger = 0
        schedule = self._single_schedule(NUM_TRACES)

        with campaign.hook(target):
            for group in schedule:
                if group == 0:
                    pub_x, pub_y = fixed_x, fixed_y
                else:
                    rnd_pub = ECC.construct(
                        curve="P-256", d=rng.randrange(1, 1 << 254)
                    ).pointQ
                    pub_x = [x for x in rnd_pub.x.to_bytes(32, "little")]
                    pub_y = [x for x in rnd_pub.y.to_bytes(32, "little")]
                campaign.expect_group(group)
                asymsca.handle_p256_ecdh(
                    private_key_array, pub_x, pub_y, cfg, trigger
                )
                resp_json = json.loads(target.read_response())
                self.assertEqual(resp_json["status"], 0)

        print("\n" + campaign.format_report(), flush=True)
        leaks = campaign.get_leaks()
        self.assertGreater(len(campaign.accumulator.sites), 0)
        self.assertEqual(len(leaks), 0)

    def test_char_p256_sign_tvla(self):
        """Run Fixed-vs-Random TVLA on cryptolib P-256 ECDSA message digest handling."""
        campaign.reset_stats()
        asymsca = OTAsymCrypto(target)
        asymsca.init()

        rng = random.Random(42)
        key = ECC.construct(curve="P-256", d=2)
        scalar = [x for x in key.d.to_bytes(32, "little")]
        pubx = [x for x in key.pointQ.x.to_bytes(32, "little")]
        puby = [x for x in key.pointQ.y.to_bytes(32, "little")]
        fixed_msg = [0 for _ in range(32)]
        cfg = 0
        trigger = 1
        schedule = self._single_schedule(NUM_TRACES)

        with campaign.hook(target):
            for group in schedule:
                msg = (
                    fixed_msg
                    if group == 0
                    else [rng.randint(0, 255) for _ in range(32)]
                )
                campaign.expect_group(group)
                asymsca.handle_p256_sign(scalar, pubx, puby, msg, cfg, trigger)
                resp_json = json.loads(target.read_response())
                self.assertEqual(resp_json["status"], 0)

        print("\n" + campaign.format_report(), flush=True)
        leaks = campaign.get_leaks()
        self.assertGreater(len(campaign.accumulator.sites), 0)
        self.assertEqual(len(leaks), 0)

    def test_char_p384_ecdh_tvla(self):
        """Run Fixed-vs-Random TVLA on cryptolib P-384 ECDH public key handling."""
        campaign.reset_stats()
        asymsca = OTAsymCrypto(target)
        asymsca.init()

        rng = random.Random(3)
        private_key = ECC.construct(curve="P-384", d=2)
        private_key_array = [x for x in private_key.d.to_bytes(48, "little")]
        fixed_pub = ECC.construct(curve="P-384", d=4833).pointQ
        fixed_x = [x for x in fixed_pub.x.to_bytes(48, "little")]
        fixed_y = [x for x in fixed_pub.y.to_bytes(48, "little")]
        cfg = 0
        trigger = 0
        schedule = self._single_schedule(NUM_TRACES)

        with campaign.hook(target):
            for group in schedule:
                if group == 0:
                    pub_x, pub_y = fixed_x, fixed_y
                else:
                    rnd_pub = ECC.construct(
                        curve="P-384", d=rng.randrange(1, 1 << 382)
                    ).pointQ
                    pub_x = [x for x in rnd_pub.x.to_bytes(48, "little")]
                    pub_y = [x for x in rnd_pub.y.to_bytes(48, "little")]
                campaign.expect_group(group)
                asymsca.handle_p384_ecdh(
                    private_key_array, pub_x, pub_y, cfg, trigger
                )
                resp_json = json.loads(target.read_response())
                self.assertEqual(resp_json["status"], 0)

        print("\n" + campaign.format_report(), flush=True)
        leaks = campaign.get_leaks()
        self.assertGreater(len(campaign.accumulator.sites), 0)
        self.assertEqual(len(leaks), 0)

    def test_char_p384_sign_tvla(self):
        """Run Fixed-vs-Random TVLA on cryptolib P-384 ECDSA message digest handling."""
        campaign.reset_stats()
        asymsca = OTAsymCrypto(target)
        asymsca.init()

        rng = random.Random(42)
        key = ECC.construct(curve="P-384", d=2)
        scalar = [x for x in key.d.to_bytes(48, "little")]
        pubx = [x for x in key.pointQ.x.to_bytes(48, "little")]
        puby = [x for x in key.pointQ.y.to_bytes(48, "little")]
        fixed_msg = [0 for _ in range(48)]
        cfg = 0
        trigger = 1
        schedule = self._single_schedule(NUM_TRACES)

        with campaign.hook(target):
            for group in schedule:
                msg = (
                    fixed_msg
                    if group == 0
                    else [rng.randint(0, 255) for _ in range(48)]
                )
                campaign.expect_group(group)
                asymsca.handle_p384_sign(scalar, pubx, puby, msg, cfg, trigger)
                resp_json = json.loads(target.read_response())
                self.assertEqual(resp_json["status"], 0)

        print("\n" + campaign.format_report(), flush=True)
        leaks = campaign.get_leaks()
        self.assertGreater(len(campaign.accumulator.sites), 0)
        self.assertEqual(len(leaks), 0)

    def test_char_ed25519_sign_tvla(self):
        """Run Fixed-vs-Random TVLA on cryptolib Ed25519 signing."""
        campaign.reset_stats()
        asymsca = OTAsymCrypto(target)
        asymsca.init()

        rng = random.Random(42)
        fixed_scalar = [0 for _ in range(32)]
        message = [i for i in range(16)]
        message_padded = utils.pad_with_zeros(message, 128)
        message_len = len(message)
        cfg = 0
        trigger = 0
        schedule = self._single_schedule(NUM_TRACES)

        with campaign.hook(target):
            for group in schedule:
                scalar = (
                    fixed_scalar
                    if group == 0
                    else [rng.randint(0, 255) for _ in range(32)]
                )
                campaign.expect_group(group)
                asymsca.handle_ed25519_sign(
                    scalar, message_padded, message_len, cfg, trigger
                )
                resp_json = json.loads(target.read_response())
                self.assertEqual(resp_json["status"], 0)

        print("\n" + campaign.format_report(), flush=True)
        leaks = campaign.get_leaks()
        self.assertGreater(len(campaign.accumulator.sites), 0)
        self.assertEqual(len(leaks), 0)

    def test_char_x25519_ecdh_tvla(self):
        """Run Fixed-vs-Random TVLA on cryptolib X25519 ECDH public key handling."""
        campaign.reset_stats()
        asymsca = OTAsymCrypto(target)
        asymsca.init()

        rng = random.Random(42)
        private_key = list(
            bytes.fromhex(
                "77076d0a7318a57d3c16c17251b26645df4c2f87ebc0992ab177fba51db92c2a"
            )
        )
        fixed_public_x = [9] + [0] * 31
        public_y = [0] * 32
        cfg = 0
        trigger = 0
        schedule = self._single_schedule(NUM_TRACES)

        with campaign.hook(target):
            for group in schedule:
                public_x = (
                    fixed_public_x
                    if group == 0
                    else self._x25519_public_key(rng.randbytes(32))
                )
                campaign.expect_group(group)
                asymsca.handle_x25519_ecdh(
                    private_key, public_x, public_y, cfg, trigger
                )
                resp_json = json.loads(target.read_response())
                self.assertEqual(resp_json["status"], 0)

        print("\n" + campaign.format_report(), flush=True)
        leaks = campaign.get_leaks()
        self.assertGreater(len(campaign.accumulator.sites), 0)
        self.assertEqual(len(leaks), 0)

    def test_char_x25519_point_mult_tvla(self):
        """Run Fixed-vs-Random TVLA on cryptolib X25519 point multiplication."""
        campaign.reset_stats()
        asymsca = OTAsymCrypto(target)
        asymsca.init()

        rng = random.Random(42)
        scalar_alice = list(
            bytes.fromhex(
                "77076d0a7318a57d3c16c17251b26645df4c2f87ebc0992ab177fba51db92c2a"
            )
        )
        fixed_scalar_bob = [9] + [0] * 31
        cfg = 0
        trigger = 0
        schedule = self._single_schedule(NUM_TRACES)

        with campaign.hook(target):
            for group in schedule:
                scalar_bob = (
                    fixed_scalar_bob
                    if group == 0
                    else self._x25519_public_key(rng.randbytes(32))
                )
                campaign.expect_group(group)
                asymsca.handle_x25519_point_mult(
                    scalar_alice, scalar_bob, cfg, trigger
                )
                resp_json = json.loads(target.read_response())
                self.assertEqual(resp_json["status"], 0)

        print("\n" + campaign.format_report(), flush=True)
        leaks = campaign.get_leaks()
        self.assertGreater(len(campaign.accumulator.sites), 0)
        self.assertEqual(len(leaks), 0)

    def test_char_rsa_sign_tvla(self):
        """Run Fixed-vs-Random TVLA on cryptolib RSA-2048 signing message encoding."""
        campaign.reset_stats()
        asymsca = OTAsymCrypto(target)
        asymsca.init()

        rng = random.Random(42)
        n_len = 256
        e = self.rsa_key.e
        d = [x for x in self.rsa_key.d.to_bytes(256, "little")]
        n = [x for x in self.rsa_key.n.to_bytes(256, "little")]
        data_len = 16
        fixed_data = list((12988).to_bytes(data_len, "little"))
        padding = 0  # kPentestRsaPaddingPkcs
        hashing = 0  # kPentestRsaHashmodeSha256
        cfg = 0
        trigger = 4  # kPentestTrigger3 around otcrypto_rsa_sign
        schedule = self._single_schedule(NUM_TRACES)

        with campaign.hook(target, function="message_encode"):
            for group in schedule:
                data = (
                    fixed_data
                    if group == 0
                    else [rng.randint(0, 255) for _ in range(data_len)]
                )
                campaign.expect_group(group)
                asymsca.handle_rsa_sign(
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
                resp_json = json.loads(target.read_response())
                self.assertEqual(resp_json["status"], 0)

        print("\n" + campaign.format_report(), flush=True)
        leaks = campaign.get_leaks()
        self.assertGreater(len(campaign.accumulator.sites), 0)
        self.assertEqual(len(leaks), 0)

    def test_char_rsa_dec_tvla(self):
        """Run Fixed-vs-Random TVLA on cryptolib RSA-2048 OAEP decryption."""
        campaign.reset_stats()
        asymsca = OTAsymCrypto(target)
        asymsca.init()

        rng = random.Random(593)
        n_len = 256
        e = self.rsa_key.e
        d = [x for x in self.rsa_key.d.to_bytes(256, "little")]
        n = [x for x in self.rsa_key.n.to_bytes(256, "little")]
        padding = 0  # OAEP
        hashing = 0  # kPentestRsaHashmodeSha256
        mode = 0  # kPentestRsa2048
        cfg = 0
        trigger = 2  # kPentestTrigger2 around otcrypto_rsa_decrypt
        schedule = self._single_schedule(NUM_TRACES)

        oaep_cipher = PKCS1_OAEP.new(
            self.rsa_key.public_key(),
            hashAlgo=SHA256,
            label=b"Test label.",
            randfunc=rng.randbytes,
        )
        fixed_ct = list(reversed(oaep_cipher.encrypt(bytes([0] * 16))))

        with campaign.hook(target, function="bignum_lt"):
            for group in schedule:
                if group == 0:
                    ct = fixed_ct
                else:
                    rnd_msg = bytes(rng.randint(0, 255) for _ in range(16))
                    ct = list(reversed(oaep_cipher.encrypt(rnd_msg)))
                campaign.expect_group(group)
                asymsca.handle_rsa_dec(
                    ct,
                    n_len,
                    e,
                    n,
                    n_len,
                    d,
                    padding,
                    hashing,
                    mode,
                    cfg,
                    trigger,
                )
                resp_json = json.loads(target.read_response())
                self.assertEqual(resp_json["status"], 0)

        print("\n" + campaign.format_report(), flush=True)
        leaks = campaign.get_leaks()
        self.assertGreater(len(campaign.accumulator.sites), 0)
        self.assertEqual(len(leaks), 0)


if __name__ == "__main__":
    unittest_argv = utils.get_selected_test_argv(
        AsymCryptolibScaTvlaGdbTest,
        requested_name=args.test,
        config_args=config_args,
        list_tests=args.list_tests,
    )

    r = Runfiles.Create()
    openocd_path = r.Rlocation(
        "lowrisc_opentitan/third_party/openocd/build_openocd/bin/openocd"
    )
    CONFIG_FILE_CHIP = r.Rlocation("openocd/tcl/interface/cmsis-dap.cfg")
    CONFIG_FILE_DESIGN = r.Rlocation(
        "lowrisc_opentitan/util/openocd/target/lowrisc-earlgrey.cfg"
    )
    opentitantool_path = r.Rlocation(
        "lowrisc_opentitan/sw/host/opentitantool/opentitantool"
    )
    gdb_bin_path = r.Rlocation(
        "lowrisc_rv32imcb_toolchain/bin/riscv32-unknown-elf-gdb"
    )
    bitstream_path = None
    if BITSTREAM:
        bitstream_path = r.Rlocation("lowrisc_opentitan/" + BITSTREAM)
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
        openocd=openocd_path,
        openocd_chip_config=CONFIG_FILE_CHIP,
        openocd_design_config=CONFIG_FILE_DESIGN,
    )

    target = targets.Target(target_cfg)
    if hasattr(target, "target") and hasattr(target.target, "gdb_port"):
        target.target.gdb_port = args.gdb_port
    campaign = GDBTVLACampaign(
        target=target,
        gdb_bin_path=gdb_bin_path,
        firmware_path=firmware_path,
        gdb_port=args.gdb_port,
        max_pc_depth=MAX_PC_DEPTH,
        workers=WORKERS,
    )

    print("Disassembly is found in ", campaign.dis_path, flush=True)

    unittest.main(argv=unittest_argv)
