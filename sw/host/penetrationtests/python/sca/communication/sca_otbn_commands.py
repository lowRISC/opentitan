# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Communication interface for the OTBN SCA application on OpenTitan.

Communication with OpenTitan happens the uJson
command interface.
"""
import json
import time
from sw.host.penetrationtests.python.util import common_library


class OTOTBN:
    def __init__(self, target) -> None:
        self.target = target

    def _ujson_otbn_sca_cmd(self):
        self.target.write(json.dumps("OtbnSca").encode("ascii"))
        time.sleep(0.003)

    def init(
        self,
        core_config: dict = common_library.default_core_config,
        sensor_config: dict = common_library.default_sensor_config,
    ) -> tuple:
        """Initializes the Otbn SCA tests on the target.

        Returns:
           Device id
           The owner info page
           The boot log
           The boot measurements
           The testOS version
        """

        # OtbnSca command.
        self._ujson_otbn_sca_cmd()
        # Init command.
        self.target.write(json.dumps("Init").encode("ascii"))

        # Write each configuration block to the target.
        self.target.write(json.dumps(core_config).encode("ascii"))
        self.target.write(json.dumps(sensor_config).encode("ascii"))

        device_id = self.target.read_response()
        owner_page = self.target.read_response()
        boot_log = self.target.read_response()
        boot_measurements = self.target.read_response()
        version = self.target.read_response()
        return device_id, owner_page, boot_log, boot_measurements, version

    def init_keymgr(self):
        """Initializes the key manager for OTBN on the target."""
        # OtbnSca command.
        self._ujson_otbn_sca_cmd()
        # Init the key manager.
        self.target.write(json.dumps("InitKeyMgr").encode("ascii"))

    def key_sideload_fvsr(self, seed: int):
        """Starts the key sidloading FvsR test on OTBN.
        Args:
            seed: The fixed seed used by the key manager.
        """
        # OtbnSca command.
        self._ujson_otbn_sca_cmd()
        # Start the KeySideloadFvsr test.
        self.target.write(json.dumps("KeySideloadFvsr").encode("ascii"))
        seed_data = {"fixed_seed": seed}
        self.target.write(json.dumps(seed_data).encode("ascii"))

    def ecdsa_p256_sign(self, masking_on: bool, msg, d0, k0):
        """Starts the EcdsaP256Sign test on OTBN.
        Args:
            masking_on: Turn on/off masking.
            msg: Message array (8xuint32_t)
            d0: Message array (10xuint32_t)
            k0: Message array (10xuint32_t)
        """
        # OtbnSca command.
        self._ujson_otbn_sca_cmd()
        # Start the EcdsaP256Sign test.
        self.target.write(json.dumps("EcdsaP256Sign").encode("ascii"))
        # Configure masking.
        masks = {"en_masks": masking_on}
        self.target.write(json.dumps(masks).encode("ascii"))
        # Send msg, d0, and k0.
        data = {"msg": msg, "d0": d0, "ko": k0}
        self.target.write(json.dumps(data).encode("ascii"))

    def ecdsa_p256_sign_batch(self, num_traces: int, masking_on: bool, msg, d0, k0):
        """Starts the EcdsaP256SignBatch test on OTBN.
        Args:
            num_traces: Number of batch operations.
            masking_on: Turn on/off masking.
            msg: Message array (8xuint32_t)
            d0: Message array (10xuint32_t)
            k0: Message array (10xuint32_t)
        """
        # OtbnSca command.
        self._ujson_otbn_sca_cmd()
        # Start the EcdsaP256SignBatch test.
        self.target.write(json.dumps("EcdsaP256Sign").encode("ascii"))
        # Configure number of traces.
        num_traces = {"num_traces": num_traces}
        self.target.write(json.dumps(num_traces).encode("ascii"))
        # Configure masking.
        masks = {"en_masks": masking_on}
        self.target.write(json.dumps(masks).encode("ascii"))
        # Send msg, d0, and k0.
        data = {"msg": msg, "d0": d0, "ko": k0}
        self.target.write(json.dumps(data).encode("ascii"))

    def ecdsa_p256_sign_batch_fvsr(
        self, num_traces: int, masking_on: bool, msg, d0, k0
    ):
        """Starts the EcdsaP256SignFvsrBatch test on OTBN.
        Args:
            num_traces: Number of batch operations.
            masking_on: Turn on/off masking.
            msg: Message array (8xuint32_t)
            d0: Message array (10xuint32_t)
            k0: Message array (10xuint32_t)
        """
        # OtbnSca command.
        self._ujson_otbn_sca_cmd()
        # Start the EcdsaP256SignBatch test.
        self.target.write(json.dumps("EcdsaP256SignFvsrBatch").encode("ascii"))
        # Configure number of traces.
        num_traces = {"num_traces": num_traces}
        self.target.write(json.dumps(num_traces).encode("ascii"))
        # Configure masking.
        masks = {"en_masks": masking_on}
        self.target.write(json.dumps(masks).encode("ascii"))
        # Send msg, d0, and k0.
        data = {"msg": msg, "d0": d0, "ko": k0}
        self.target.write(json.dumps(data).encode("ascii"))

    def start_combi_ops_batch(
        self, num_iterations, fixed_data1, fixed_data2, print_flag, trigger
    ):
        """Start the combi ops app in batch mode.
        Args:
            num_iterations: How many traces per batch.
            fixed_data1: The first fixed input.
            fixed_data2: The second fixed input.
            print_flag: Whether to print an output or an empty RESP_OK.
            trigger: Which triggers to raise.
        """
        # OtbnSca command.
        self._ujson_otbn_sca_cmd()
        # Start the CombiOps test.
        self.target.write(json.dumps("CombiOps").encode("ascii"))
        data = {
            "num_iterations": num_iterations,
            "fixed_data1": fixed_data1,
            "fixed_data2": fixed_data2,
            "print_flag": print_flag,
            "trigger": trigger,
        }
        self.target.write(json.dumps(data).encode("ascii"))

    def sha2_single(
        self,
        msg: list[int],
        msg_len: int,
        mode: int = 0,
        en_masks: bool = True,
    ):
        """Runs a single OTBN SHA-2 (SHA-256/384/512) operation.
        Args:
            msg: Input message bytes (up to 64 bytes).
            msg_len: Active length of the message in bytes (0..64).
            mode: 0 (or 256) for SHA-256, 1 (or 384) for SHA-384, 2 (or 512) for SHA-512.
            en_masks: Enable or disable boolean input masking.
        """
        self._ujson_otbn_sca_cmd()
        self.target.write(json.dumps("Sha2Single").encode("ascii"))
        time.sleep(0.003)
        cfg = {
            "msg": list(msg),
            "msg_len": msg_len,
            "mode": mode,
            "en_masks": en_masks,
        }
        self.target.write(json.dumps(cfg).encode("ascii"))

    def sha2_batch_fvsr(
        self,
        num_traces: int,
        msg: list[int],
        msg_len: int,
        mode: int = 0,
        en_masks: bool = True,
    ):
        """Runs OTBN SHA-2 (SHA-256/384/512) in Fixed-vs-Random batch mode.
        Args:
            num_traces: Number of traces in the batch.
            msg: Fixed message bytes (up to 64 bytes).
            msg_len: Active length of each message in bytes (0..64).
            mode: 0 (or 256) for SHA-256, 1 (or 384) for SHA-384, 2 (or 512) for SHA-512.
            en_masks: Enable or disable boolean input masking.
        """
        self._ujson_otbn_sca_cmd()
        self.target.write(json.dumps("Sha2BatchFvsr").encode("ascii"))
        time.sleep(0.003)
        self.target.write(
            json.dumps({"num_traces": num_traces}).encode("ascii")
        )
        cfg = {
            "msg": list(msg),
            "msg_len": msg_len,
            "mode": mode,
            "en_masks": en_masks,
        }
        self.target.write(json.dumps(cfg).encode("ascii"))

    def sha2_batch_random(
        self,
        num_traces: int,
        msg_len: int,
        mode: int = 0,
        en_masks: bool = True,
    ):
        """Runs OTBN SHA-2 (SHA-256/384/512) in Random batch mode.
        Args:
            num_traces: Number of traces in the batch.
            msg_len: Active length of each random message in bytes (0..64).
            mode: 0 (or 256) for SHA-256, 1 (or 384) for SHA-384, 2 (or 512) for SHA-512.
            en_masks: Enable or disable boolean input masking.
        """
        self._ujson_otbn_sca_cmd()
        self.target.write(json.dumps("Sha2BatchRandom").encode("ascii"))
        time.sleep(0.003)
        self.target.write(
            json.dumps({"num_traces": num_traces}).encode("ascii")
        )
        cfg = {
            "msg": [0] * 64,
            "msg_len": msg_len,
            "mode": mode,
            "en_masks": en_masks,
        }
        self.target.write(json.dumps(cfg).encode("ascii"))

    def hkdf_single(
        self,
        ikm: list[int],
        ikm_len: int,
        salt: list[int],
        salt_len: int,
        info: list[int],
        info_len: int,
        okm_blocks: int = 1,
        mode: int = 0,
        en_masks: bool = True,
    ):
        """Runs a single OTBN HKDF (HKDF-SHA-256/384/512) operation.
        Args:
            ikm: Input keying material bytes (up to 64 bytes).
            ikm_len: Active length of IKM in bytes (0..64).
            salt: Salt bytes (up to 64 bytes).
            salt_len: Active length of salt in bytes (0..64).
            info: Context info bytes (up to 64 bytes).
            info_len: Active length of info in bytes (0..64).
            okm_blocks: Number of digest-sized output blocks to expand.
            mode: 0 (or 256) for SHA-256, 1 (or 384) for SHA-384, 2 (or 512) for SHA-512.
            en_masks: Enable or disable boolean input masking.
        """
        self._ujson_otbn_sca_cmd()
        self.target.write(json.dumps("HkdfSingle").encode("ascii"))
        time.sleep(0.003)
        cfg = {
            "ikm": list(ikm),
            "ikm_len": ikm_len,
            "salt": list(salt),
            "salt_len": salt_len,
            "info": list(info),
            "info_len": info_len,
            "okm_blocks": okm_blocks,
            "mode": mode,
            "en_masks": en_masks,
        }
        self.target.write(json.dumps(cfg).encode("ascii"))

    def hkdf_batch_fvsr(
        self,
        num_traces: int,
        ikm: list[int],
        ikm_len: int,
        salt: list[int],
        salt_len: int,
        info: list[int],
        info_len: int,
        okm_blocks: int = 1,
        mode: int = 0,
        en_masks: bool = True,
    ):
        """Runs OTBN HKDF (HKDF-SHA-256/384/512) in Fixed-vs-Random batch mode.
        Args:
            num_traces: Number of traces in the batch.
            ikm: Fixed input keying material bytes (up to 64 bytes).
            ikm_len: Active length of IKM in bytes (0..64).
            salt: Fixed salt bytes (up to 64 bytes).
            salt_len: Active length of salt in bytes (0..64).
            info: Fixed context info bytes (up to 64 bytes).
            info_len: Active length of info in bytes (0..64).
            okm_blocks: Number of digest-sized output blocks to expand.
            mode: 0 (or 256) for SHA-256, 1 (or 384) for SHA-384, 2 (or 512) for SHA-512.
            en_masks: Enable or disable boolean input masking.
        """
        self._ujson_otbn_sca_cmd()
        self.target.write(json.dumps("HkdfBatchFvsr").encode("ascii"))
        time.sleep(0.003)
        self.target.write(
            json.dumps({"num_traces": num_traces}).encode("ascii")
        )
        cfg = {
            "ikm": list(ikm),
            "ikm_len": ikm_len,
            "salt": list(salt),
            "salt_len": salt_len,
            "info": list(info),
            "info_len": info_len,
            "okm_blocks": okm_blocks,
            "mode": mode,
            "en_masks": en_masks,
        }
        self.target.write(json.dumps(cfg).encode("ascii"))

    def hkdf_batch_random(
        self,
        num_traces: int,
        ikm_len: int,
        salt_len: int,
        info: list[int],
        info_len: int,
        okm_blocks: int = 1,
        mode: int = 0,
        en_masks: bool = True,
    ):
        """Runs OTBN HKDF (HKDF-SHA-256/384/512) in Random batch mode.
        Args:
            num_traces: Number of traces in the batch.
            ikm_len: Active length of random IKM in bytes (0..64).
            salt_len: Active length of random salt in bytes (0..64).
            info: Fixed context info bytes (up to 64 bytes).
            info_len: Active length of info in bytes (0..64).
            okm_blocks: Number of digest-sized output blocks to expand.
            mode: 0 (or 256) for SHA-256, 1 (or 384) for SHA-384, 2 (or 512) for SHA-512.
            en_masks: Enable or disable boolean input masking.
        """
        self._ujson_otbn_sca_cmd()
        self.target.write(json.dumps("HkdfBatchRandom").encode("ascii"))
        time.sleep(0.003)
        self.target.write(
            json.dumps({"num_traces": num_traces}).encode("ascii")
        )
        cfg = {
            "ikm": [0] * 64,
            "ikm_len": ikm_len,
            "salt": [0] * 64,
            "salt_len": salt_len,
            "info": list(info),
            "info_len": info_len,
            "okm_blocks": okm_blocks,
            "mode": mode,
            "en_masks": en_masks,
        }
        self.target.write(json.dumps(cfg).encode("ascii"))
