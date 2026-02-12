# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Communication interface for the SHA3 SCA application on OpenTitan.

Communication with OpenTitan happens over the uJson
command interface.
"""
import json
import time
from typing import Optional
from sw.host.penetrationtests.python.util import common_library


class OTSHA3:
    def __init__(self, target) -> None:
        self.target = target

    def _ujson_sha3_sca_cmd(self):
        self.target.write(json.dumps("Sha3Sca").encode("ascii"))
        time.sleep(0.003)

    def init(
        self,
        fpga_mode_bit: int,
        core_config: dict = common_library.default_core_config,
        sensor_config: dict = common_library.default_sensor_config,
    ) -> tuple:
        """Initializes SHA3 on the target.
        Args:
            fpga_mode_bit: Indicates whether FPGA specific KMAC test is started.
        Returns:
            Device id
            The owner info page
            The boot log
            The boot measurements
            The testOS version
        """

        # Sha3Sca command.
        self._ujson_sha3_sca_cmd()
        # Init the SHA3 core.
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

    def _ujson_sha3_sca_ack(self, num_attempts: Optional[int] = 100):
        # Wait for ack.
        read_counter = 0
        while read_counter < num_attempts:
            read_line = str(self.target.readline())
            if "RESP_OK" in read_line:
                json_string = read_line.split("RESP_OK:")[1].split(" CRC:")[0]
                try:
                    if "status" in json_string:
                        status = json.loads(json_string)["status"]
                        if status != 0:
                            raise Exception(
                                "Acknowledge error: Device and host not in sync"
                            )
                        return status
                except Exception:
                    raise Exception("Acknowledge error: Device and host not in sync")
            else:
                read_counter += 1
        raise Exception("Acknowledge error: Device and host not in sync")

    def set_mask_off(self):
        # Sha3Sca command.
        self._ujson_sha3_sca_cmd()
        # DisableMasking command.
        self.target.write(json.dumps("DisableMasking").encode("ascii"))
        # Num_segments payload.
        mask = {"masks_off": 1}
        self.target.write(json.dumps(mask).encode("ascii"))
        # Wait for ack.
        self._ujson_sha3_sca_ack()

    def set_mask_on(self):
        # Sha3Sca command.
        self._ujson_sha3_sca_cmd()
        # DisableMasking command.
        self.target.write(json.dumps("DisableMasking").encode("ascii"))
        # Num_segments payload.
        mask = {"masks_off": 0}
        self.target.write(json.dumps(mask).encode("ascii"))
        # Wait for ack.
        self._ujson_sha3_sca_ack()

    def absorb(self, text, text_length: Optional[int] = 16):
        """Write plaintext to OpenTitan SHA3 & start absorb.
        Args:
            text: The plaintext bytearray.
        """
        # Sha3Sca command.
        self._ujson_sha3_sca_cmd()
        # SingleAbsorb command.
        self.target.write(json.dumps("SingleAbsorb").encode("ascii"))
        # SingleAbsorb payload.
        text_int = [x for x in text]
        text_data = {"msg": text_int, "msg_length": text_length}
        self.target.write(json.dumps(text_data).encode("ascii"))

    def absorb_batch(self, num_segments):
        """Start absorb for batch.
        Args:
            num_segments: Number of hashings to perform.
        """
        # Sha3Sca command.
        self._ujson_sha3_sca_cmd()
        # Batch command.
        self.target.write(json.dumps("Batch").encode("ascii"))
        # Num_segments payload.
        num_segments_data = {"num_enc": num_segments}
        self.target.write(json.dumps(num_segments_data).encode("ascii"))
        # Wait for ack.
        self._ujson_sha3_sca_ack()

    def write_lfsr_seed(self, seed):
        """Seed the LFSR.
        Args:
            seed: The 4-byte seed.
        """
        # Sha3Sca command.
        self._ujson_sha3_sca_cmd()
        # SeedLfsr command.
        self.target.write(json.dumps("SeedLfsr").encode("ascii"))
        # Seed payload.
        seed_int = [x for x in seed]
        seed_data = {"seed": seed_int}
        self.target.write(json.dumps(seed_data).encode("ascii"))

    def fvsr_fixed_msg_set(self, msg, msg_length: Optional[int] = 16):
        """Write the fixed message to SHA3.
        Args:
            msg: Bytearray containing the message.
        """
        # Sha3Sca command.
        self._ujson_sha3_sca_cmd()
        # FixedMessageSet command.
        self.target.write(json.dumps("FixedMessageSet").encode("ascii"))
        # Msg payload.
        msg_int = [x for x in msg]
        msg_data = {"msg": msg_int, "msg_length": msg_length}
        self.target.write(json.dumps(msg_data).encode("ascii"))
