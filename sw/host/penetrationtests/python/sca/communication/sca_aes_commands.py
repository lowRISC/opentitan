# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Communication interface for the AES SCA application on OpenTitan.

Communication with OpenTitan happens over the uJson
command interface.
"""
import json
import time
from sw.host.penetrationtests.python.util import common_library


class OTAES:
    def __init__(self, target) -> None:
        self.target = target

    def _ujson_aes_sca_cmd(self):
        self.target.write(json.dumps("AesSca").encode("ascii"))
        time.sleep(0.003)

    def init(
        self,
        fpga_mode_bit: int,
        core_config: dict = common_library.default_core_config,
        sensor_config: dict = common_library.default_sensor_config,
    ) -> tuple:
        """Initializes AES on the target.
        Args:
            fpga_mode_bit: Indicates whether FPGA specific AES test is started.

        Returns:
            Device id
            The owner info page
            The boot log
            The boot measurements
            The testOS version
        """

        # AesSca command.
        self._ujson_aes_sca_cmd()
        # Init the AES core.
        self.target.write(json.dumps("Init").encode("ascii"))
        # FPGA mode.
        fpga_mode = {"fpga_mode": fpga_mode_bit}
        self.target.write(json.dumps(fpga_mode).encode("ascii"))

        # Write each configuration block to the target.
        self.target.write(json.dumps(core_config).encode("ascii"))
        self.target.write(json.dumps(sensor_config).encode("ascii"))

        device_id = self.target.read_response()
        owner_page = self.target.read_response()
        boot_log = self.target.read_response()
        boot_measurements = self.target.read_response()
        version = self.target.read_response()
        return device_id, owner_page, boot_log, boot_measurements, version

    def seed_lfsr(self, seed):
        """Seed the LFSR.
        Args:
            seed: The 4-byte seed.
        """
        # AesSca command.
        self._ujson_aes_sca_cmd()
        # SeedLfsr command.
        self.target.write(json.dumps("SeedLfsr").encode("ascii"))
        # Seed payload.
        seed_data = {"seed": [x for x in seed]}
        self.target.write(json.dumps(seed_data).encode("ascii"))

    def batch_daisy_chain(self, num_segments, key, text):
        """Start encryption for batch (alternative).
        Args:
            key: Key to use for all encryptions.
            text: First plaintext to use.
            num_segments: Number of encryptions to perform.
        """
        # AesSca command.
        self._ujson_aes_sca_cmd()
        # BatchAlternativeEncrypt command.
        self.target.write(json.dumps("BatchDaisy").encode("ascii"))
        key_data = {"key": key, "key_length": len(key)}
        self.target.write(json.dumps(key_data).encode("ascii"))
        text_data = {"text": text, "text_length": len(text)}
        self.target.write(json.dumps(text_data).encode("ascii"))
        num_encryption_data = {"num_enc": num_segments}
        self.target.write(json.dumps(num_encryption_data).encode("ascii"))

    def batch_fvsr_data(self, num_segments, key, text):
        """Start encryption for batch fixed vs. random plaintext.
        Args:
            key: Key to use for all encryptions.
            text: The fixed plaintext to use.
            num_segments: Number of encryptions to perform.
        """
        # AesSca command.
        self._ujson_aes_sca_cmd()
        # BatchFvsrData command.
        self.target.write(json.dumps("BatchFvsrData").encode("ascii"))
        key_data = {"key": key, "key_length": len(key)}
        self.target.write(json.dumps(key_data).encode("ascii"))
        text_data = {"text": text, "text_length": len(text)}
        self.target.write(json.dumps(text_data).encode("ascii"))
        num_encryption_data = {"num_enc": num_segments}
        self.target.write(json.dumps(num_encryption_data).encode("ascii"))

    def batch_fvsr_key(self, num_segments, key):
        """Start batch encryption for FVSR key.
        Args:
            key: Fixed key to use.
            num_segments: Number of encryptions to perform.
        """
        # AesSca command.
        self._ujson_aes_sca_cmd()
        # BatchFvsrKey command.
        self.target.write(json.dumps("BatchFvsrKey").encode("ascii"))
        key_data = {"key": key, "key_length": len(key)}
        self.target.write(json.dumps(key_data).encode("ascii"))
        num_encryption_data = {"num_enc": num_segments}
        self.target.write(json.dumps(num_encryption_data).encode("ascii"))

    def batch_random(self, num_segments, key):
        """Start batch encryption for FVSR data.
        Args:
            key: Key to use for all encryptions.
            num_segments: Number of encryptions to perform.
        """
        # AesSca command.
        self._ujson_aes_sca_cmd()
        # BatchRandom command.
        self.target.write(json.dumps("BatchRandom").encode("ascii"))
        key_data = {"key": key, "key_length": len(key)}
        self.target.write(json.dumps(key_data).encode("ascii"))
        num_encryption_data = {"num_enc": num_segments}
        self.target.write(json.dumps(num_encryption_data).encode("ascii"))

    def single_encrypt(self, key, text):
        """Write plaintext to OpenTitan AES & start encryption.
        Args:
            key: The key.
            text: The plaintext.
        """
        # AesSca command.
        self._ujson_aes_sca_cmd()
        # Single command.
        self.target.write(json.dumps("Single").encode("ascii"))
        key_data = {"key": key, "key_length": len(key)}
        self.target.write(json.dumps(key_data).encode("ascii"))
        text_data = {"text": text, "text_length": len(text)}
        self.target.write(json.dumps(text_data).encode("ascii"))
