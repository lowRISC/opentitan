# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import json
import os
import random
import unittest
from Crypto.Cipher import AES
from Crypto.Hash import CMAC, HMAC, SHA256
from python.runfiles import Runfiles
from sw.host.penetrationtests.python.sca.communication.sca_sym_cryptolib_commands import (
    OTSymCrypto,
)
from sw.host.penetrationtests.python.sca.host_scripts import sca_sym_cryptolib_functions
from sw.host.penetrationtests.python.util import targets
from sw.host.penetrationtests.python.util import utils
from sw.host.penetrationtests.python.util.gdb_tvla import GDBTVLACampaign

ignored_keys_set = set([])
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


class SymCryptolibScaTvlaGdbTest(unittest.TestCase):

    @classmethod
    def setUpClass(cls):
        if target is None:
            raise RuntimeError("Target failed to initialize.")
        target.initialize_target()
        OTSymCrypto(target).init()

    def setUp(self):
        if getattr(getattr(target, "target", None), "_faulted", False):
            target.reset_target()
            OTSymCrypto(target).init()

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

    def test_char_aes_fvsr_plaintext_tvla(self):
        """Hook char_aes_fvsr_plaintext and inspect Ibex RF leakage during cryptolib AES."""
        campaign.reset_stats()
        iterations, num_iterations = self._batch_params(NUM_TRACES)
        data_len = 16
        data = [0 for _ in range(data_len)]
        key_len = 16
        key = [i for i in range(key_len)]
        iv = [0 for _ in range(16)]
        padding = 0  # kPentestAesPaddingNull
        mode = 0  # kPentestAesModeEcb
        op_enc = True
        cfg = 0
        trigger = 0

        groups, batch_data = self._fvsr_schedule(
            iterations, num_iterations, data
        )

        with campaign.hook(target, groups=groups):
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
                num_iterations,
                reset=False,
            )
        actual_result_json = json.loads(actual_result)

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
        print("\n" + campaign.format_report(), flush=True)
        leaks = campaign.get_leaks()
        self.assertGreater(len(campaign.accumulator.sites), 0)
        self.assertEqual(len(leaks), 0)

    def test_char_cmac_fvsr_plaintext_tvla(self):
        """Hook char_cmac_fvsr_plaintext and inspect Ibex RF leakage during cryptolib CMAC."""
        campaign.reset_stats()
        iterations, num_iterations = self._batch_params(NUM_TRACES)
        data_len = 16
        data = [0 for _ in range(data_len)]
        key_len = 16
        key = [i for i in range(key_len)]
        iv = [0 for _ in range(16)]
        cfg = 0
        trigger = 0

        groups, batch_data = self._fvsr_schedule(
            iterations, num_iterations, data
        )

        with campaign.hook(target, groups=groups):
            actual_result = sca_sym_cryptolib_functions.char_cmac_fvsr_plaintext(
                target,
                iterations,
                data,
                data_len,
                key,
                key_len,
                iv,
                cfg,
                trigger,
                num_iterations,
                reset=False,
            )
        actual_result_json = json.loads(actual_result)

        cmac = CMAC.new(bytes(key), ciphermod=AES)
        cmac.update(bytes(batch_data))
        expected_result = utils.pad_with_zeros([x for x in cmac.digest()], 64)
        expected_result_json = {
            "status": 0,
            "data": expected_result,
            "data_len": 16,
            "cfg": 0,
        }
        utils.compare_json_data(
            actual_result_json, expected_result_json, ignored_keys_set
        )
        print("\n" + campaign.format_report(), flush=True)
        leaks = campaign.get_leaks()
        self.assertGreater(len(campaign.accumulator.sites), 0)
        self.assertEqual(len(leaks), 0)

    def test_char_gcm_fvsr_plaintext_tvla(self):
        """Hook char_gcm_fvsr_plaintext and inspect Ibex RF leakage during cryptolib AES-GCM."""
        campaign.reset_stats()
        iterations, num_iterations = self._batch_params(NUM_TRACES)
        data_len = 16
        data = [0 for _ in range(data_len)]
        aad_len = 16
        aad = [0 for _ in range(aad_len)]
        key_len = 16
        key = [i for i in range(key_len)]
        iv = [0 for _ in range(16)]
        cfg = 0
        trigger = 0

        groups, batch_data = self._fvsr_schedule(
            iterations, num_iterations, data
        )

        with campaign.hook(
            target,
            groups=groups,
            skip_functions=[
                "galois_mul_state_key",
                "ghash_process_block",
                "ghash_init_subkey",
                "ghash_context_integrity_checksum",
            ],
        ):
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
                num_iterations,
                reset=False,
            )
        actual_result_json = json.loads(actual_result)

        cipher_gen = AES.new(bytes(key), AES.MODE_GCM, bytes(iv))
        cipher_gen.update(bytes(aad))
        expected_ciphertext, expected_tag = cipher_gen.encrypt_and_digest(
            bytes(batch_data)
        )
        expected_result_json = {
            "status": 0,
            "data": utils.pad_with_zeros([x for x in expected_ciphertext], 64),
            "data_len": data_len,
            "tag": utils.pad_with_zeros([x for x in expected_tag], 64),
            "tag_len": 16,
            "cfg": 0,
        }
        utils.compare_json_data(
            actual_result_json, expected_result_json, ignored_keys_set
        )
        print("\n" + campaign.format_report(), flush=True)
        leaks = campaign.get_leaks()
        self.assertGreater(len(campaign.accumulator.sites), 0)
        self.assertEqual(len(leaks), 0)

    def test_char_hmac_fvsr_plaintext_tvla(self):
        """Hook char_hmac_fvsr_plaintext and inspect Ibex RF leakage during cryptolib HMAC."""
        campaign.reset_stats()
        iterations, num_iterations = self._batch_params(NUM_TRACES)
        data_len = 32
        data = [0 for _ in range(data_len)]
        key_len = 32
        key = [i for i in range(key_len)]
        padding = 0
        mode = 0  # kPentestHmacHashAlgSha256
        cfg = 0
        trigger = 0

        groups, batch_data = self._fvsr_schedule(
            iterations, num_iterations, data
        )

        with campaign.hook(target, groups=groups):
            actual_result = sca_sym_cryptolib_functions.char_hmac_fvsr_plaintext(
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
                num_iterations,
                reset=False,
            )
        actual_result_json = json.loads(actual_result)

        sha256 = HMAC.new(key=bytes(key), digestmod=SHA256)
        sha256.update(bytes(batch_data))
        expected_result = utils.pad_with_zeros([x for x in sha256.digest()], 64)
        expected_result_json = {
            "status": 0,
            "data": expected_result,
            "data_len": 32,
            "cfg": 0,
        }
        utils.compare_json_data(
            actual_result_json, expected_result_json, ignored_keys_set
        )
        print("\n" + campaign.format_report(), flush=True)
        leaks = campaign.get_leaks()
        self.assertGreater(len(campaign.accumulator.sites), 0)
        self.assertEqual(len(leaks), 0)

    def test_char_drbg_reseed_tvla(self):
        """Run Fixed-vs-Random TVLA on cryptolib DRBG reseed/instantiate."""
        campaign.reset_stats()
        symsca = OTSymCrypto(target)
        symsca.init()

        rng = random.Random(42)
        entropy_len = 32
        fixed_entropy = [0 for _ in range(entropy_len)]
        nonce_len = 16
        nonce = [0 for _ in range(nonce_len)]
        reseed_interval = 100
        mode = 0
        cfg = 0
        trigger = 1  # kPentestTrigger1 around otcrypto_drbg_instantiate
        schedule = self._single_schedule(NUM_TRACES)

        with campaign.hook(target):
            for group in schedule:
                entropy = (
                    fixed_entropy
                    if group == 0
                    else [rng.randint(0, 255) for _ in range(entropy_len)]
                )
                campaign.expect_group(group)
                symsca.handle_drbg_reseed(
                    entropy,
                    entropy_len,
                    nonce,
                    nonce_len,
                    reseed_interval,
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
        SymCryptolibScaTvlaGdbTest,
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
