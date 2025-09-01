# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Communication interface for the HMAC SCA application on OpenTitan.

Communication with OpenTitan happens over the uJSON command interface.
"""
import json
import time
from sw.host.penetrationtests.python.util import common_library


class OTHMAC:
    def __init__(self, target) -> None:
        self.target = target

    def _ujson_hmac_sca_cmd(self):
        self.target.write(json.dumps("HmacSca").encode("ascii"))
        time.sleep(0.003)

    def init(
        self,
        core_config: dict = common_library.default_core_config,
        sensor_config: dict = common_library.default_sensor_config,
    ) -> tuple:
        """Initializes HMAC on the target.

        Returns:
            Device id
            The owner info page
            The boot log
            The boot measurements
            The testOS version
        """

        # HmacSca command.
        self._ujson_hmac_sca_cmd()
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

    def single(self, msg: list[int], key: list[int], trigger: int):
        """Start a single HMAC operation using the given message and key.
        Args:
            msg: The list containing the message.
            key: The key containing the message.
            trigger: Which trigger to raise.
        """
        # HmacSca command.
        self._ujson_hmac_sca_cmd()
        # Single command.
        self.target.write(json.dumps("Single").encode("ascii"))
        # Key payload.
        # Key payload.
        key_data = {"key": key}
        key_data = {"key": key}
        self.target.write(json.dumps(key_data).encode("ascii"))
        # Message payload.
        msg_data = {"message": msg}
        self.target.write(json.dumps(msg_data).encode("ascii"))
        # Trigger payload.
        if trigger == 0:
            mode = {
                "start_trigger": True,
                "msg_trigger": False,
                "process_trigger": False,
                "finish_trigger": False,
            }
        elif trigger == 1:
            mode = {
                "start_trigger": False,
                "msg_trigger": True,
                "process_trigger": False,
                "finish_trigger": False,
            }
        elif trigger == 2:
            mode = {
                "start_trigger": False,
                "msg_trigger": False,
                "process_trigger": True,
                "finish_trigger": False,
            }
        elif trigger == 3:
            mode = {
                "start_trigger": False,
                "msg_trigger": False,
                "process_trigger": False,
                "finish_trigger": True,
            }
        self.target.write(json.dumps(mode).encode("ascii"))

    def fvsr_batch(self, key: list[int], num_segments: int, trigger: int):
        """Start num_segments HMAC operation in FvsR batch mode.
        Args:
            key: The key containing the message.
            num_segments: The number of iterations.
            trigger: Which trigger to raise.
        """
        # HmacSca command.
        self._ujson_hmac_sca_cmd()
        # BatchFvsr command.
        self.target.write(json.dumps("BatchFvsr").encode("ascii"))
        # Key payload.
        key_data = {"key": key}
        self.target.write(json.dumps(key_data).encode("ascii"))
        # Number of iterations payload.
        num_it_data = {"num_iterations": num_segments}
        self.target.write(json.dumps(num_it_data).encode("ascii"))
        # Trigger payload.
        if trigger == 0:
            mode = {
                "start_trigger": True,
                "msg_trigger": False,
                "process_trigger": False,
                "finish_trigger": False,
            }
        elif trigger == 1:
            mode = {
                "start_trigger": False,
                "msg_trigger": True,
                "process_trigger": False,
                "finish_trigger": False,
            }
        elif trigger == 2:
            mode = {
                "start_trigger": False,
                "msg_trigger": False,
                "process_trigger": True,
                "finish_trigger": False,
            }
        elif trigger == 3:
            mode = {
                "start_trigger": False,
                "msg_trigger": False,
                "process_trigger": False,
                "finish_trigger": True,
            }
        self.target.write(json.dumps(mode).encode("ascii"))

    def random_batch(self, num_segments: int, trigger: int):
        """Start num_segments HMAC operations in random batch mode.
        Args:
            num_segments: The number of iterations.
            trigger: Which trigger to raise.
        """
        # HmacSca command.
        self._ujson_hmac_sca_cmd()
        # BatchRandom command.
        self.target.write(json.dumps("BatchRandom").encode("ascii"))
        # Number of iterations payload.
        num_it_data = {"num_iterations": num_segments}
        self.target.write(json.dumps(num_it_data).encode("ascii"))
        # Trigger payload.
        if trigger == 0:
            mode = {
                "start_trigger": True,
                "msg_trigger": False,
                "process_trigger": False,
                "finish_trigger": False,
            }
        elif trigger == 1:
            mode = {
                "start_trigger": False,
                "msg_trigger": True,
                "process_trigger": False,
                "finish_trigger": False,
            }
        elif trigger == 2:
            mode = {
                "start_trigger": False,
                "msg_trigger": False,
                "process_trigger": True,
                "finish_trigger": False,
            }
        elif trigger == 3:
            mode = {
                "start_trigger": False,
                "msg_trigger": False,
                "process_trigger": False,
                "finish_trigger": True,
            }
        self.target.write(json.dumps(mode).encode("ascii"))

    def daisy_chain(
        self, text: list[int], key: list[int], num_segments: int, trigger: int
    ):
        """Start num_segments HMAC operations in daisy chain mode.
        Args:
            text: The input message
            key: The HMAC key
            num_segments: The number of iterations.
            trigger: Which trigger to raise.
        """
        # HmacSca command.
        self._ujson_hmac_sca_cmd()
        # BatchRandom command.
        self.target.write(json.dumps("BatchDaisy").encode("ascii"))
        # Number of iterations payload.
        key_data = {"key": key}
        self.target.write(json.dumps(key_data).encode("ascii"))
        message_data = {"message": text}
        self.target.write(json.dumps(message_data).encode("ascii"))
        num_it_data = {"num_iterations": num_segments}
        self.target.write(json.dumps(num_it_data).encode("ascii"))
        # Trigger payload.
        if trigger == 0:
            mode = {
                "start_trigger": True,
                "msg_trigger": False,
                "process_trigger": False,
                "finish_trigger": False,
            }
        elif trigger == 1:
            mode = {
                "start_trigger": False,
                "msg_trigger": True,
                "process_trigger": False,
                "finish_trigger": False,
            }
        elif trigger == 2:
            mode = {
                "start_trigger": False,
                "msg_trigger": False,
                "process_trigger": True,
                "finish_trigger": False,
            }
        elif trigger == 3:
            mode = {
                "start_trigger": False,
                "msg_trigger": False,
                "process_trigger": False,
                "finish_trigger": True,
            }
        self.target.write(json.dumps(mode).encode("ascii"))
