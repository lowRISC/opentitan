# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Communication interface for the KMAC SCA application on OpenTitan.

Communication with OpenTitan happens over the uJson
command interface.
"""
import json
import time
from typing import Optional
from sw.host.penetrationtests.python.util import common_library


class OTKMAC:
    def __init__(self, target) -> None:
        self.target = target

    def _ujson_kmac_sca_cmd(self):
        self.target.write(json.dumps("KmacSca").encode("ascii"))
        time.sleep(0.003)

    def init(
        self,
        fpga_mode_bit: int,
        core_config: dict = common_library.default_core_config,
        sensor_config: dict = common_library.default_sensor_config,
    ) -> tuple:
        """Initializes KMAC on the target.
        Args:
            fpga_mode_bit: Indicates whether FPGA specific KMAC test is started.

         Returns:
            Device id
            The owner info page
            The boot log
            The boot measurements
            The testOS version
        """

        # KmacSca command.
        self._ujson_kmac_sca_cmd()
        # Init command.
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

    def write_key(self, key: list[int]):
        """Write the key to KMAC.
        Args:
            key: Bytearray containing the key.
        """
        # KmacSca command.
        self._ujson_kmac_sca_cmd()
        # SetKey command.
        self.target.write(json.dumps("SetKey").encode("ascii"))
        # Key payload.
        key_data = {"key": key, "key_length": 16}
        self.target.write(json.dumps(key_data).encode("ascii"))

    def fvsr_key_set(self, key: list[int], key_length: Optional[int] = 16):
        """Write the fixed key to KMAC.
        Args:
            key: Bytearray containing the key.
        """
        # KmacSca command.
        self._ujson_kmac_sca_cmd()
        # SetKey command.
        self.target.write(json.dumps("FixedKeySet").encode("ascii"))
        # FixedKeySet payload.
        key_data = {"key": key, "key_length": key_length}
        self.target.write(json.dumps(key_data).encode("ascii"))

    def write_lfsr_seed(self, seed):
        """Seed the LFSR.
        Args:
            seed: The 4-byte seed.
        """
        # KmacSca command.
        self._ujson_kmac_sca_cmd()
        # SeedLfsr command.
        self.target.write(json.dumps("SeedLfsr").encode("ascii"))
        # Seed payload.
        seed_int = [x for x in seed]
        seed_data = {"seed": seed_int}
        self.target.write(json.dumps(seed_data).encode("ascii"))

    def absorb_batch(self, num_segments):
        """Start absorb for batch.
        Args:
            num_segments: Number of encryptions to perform.
        """
        # KmacSca command.
        self._ujson_kmac_sca_cmd()
        # Batch command.
        self.target.write(json.dumps("Batch").encode("ascii"))
        # Num_segments payload.
        num_segments_data = {"num_enc": num_segments}
        self.target.write(json.dumps(num_segments_data).encode("ascii"))

    def absorb_daisy_chain(self, text, key, num_segments):
        """Start absorb for daisy chain batch.
        Args:
            num_segments: Number of encryptions to perform.
            text: The input message
            key: The KMAC128 key
        """
        # KmacSca command.
        self._ujson_kmac_sca_cmd()
        # BatchDaisy command.
        self.target.write(json.dumps("BatchDaisy").encode("ascii"))
        # Num_segments payload.
        num_it_data = {"num_enc": num_segments}
        self.target.write(json.dumps(num_it_data).encode("ascii"))
        message_data = {"msg": text, "msg_length": len(text)}
        self.target.write(json.dumps(message_data).encode("ascii"))
        key_data = {"key": key, "key_length": len(key)}
        self.target.write(json.dumps(key_data).encode("ascii"))

    def absorb(self, text, text_length: Optional[int] = 16):
        """Write plaintext to OpenTitan KMAC & start absorb.
        Args:
            text: The plaintext bytearray.
        """
        # KmacSca command.
        self._ujson_kmac_sca_cmd()
        # SingleAbsorb command.
        self.target.write(json.dumps("SingleAbsorb").encode("ascii"))
        # Msg payload.
        text_int = [x for x in text]
        text_data = {"msg": text_int, "msg_length": text_length}
        self.target.write(json.dumps(text_data).encode("ascii"))
