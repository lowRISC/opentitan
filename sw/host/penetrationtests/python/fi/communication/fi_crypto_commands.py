# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Communication interface for OpenTitan Crypto FI framework.

Communication with OpenTitan happens over the uJSON command interface.
"""
import json
import time
from sw.host.penetrationtests.python.util import common_library


class OTFICrypto:
    def __init__(self, target) -> None:
        self.target = target

    def _ujson_crypto_cmd(self) -> None:
        self.target.write(json.dumps("CryptoFi").encode("ascii"))
        time.sleep(0.003)

    def init(
        self,
        core_config: dict = common_library.default_core_config,
        sensor_config: dict = common_library.default_sensor_config,
        alert_config: dict = common_library.default_alert_config,
    ) -> tuple:
        """Initialize the Crypto FI code on the chip.

        Returns:
            Device id
            The owner info page
            The boot log
            The boot measurements
            The testOS version
        """

        # CryptoFi command.
        self._ujson_crypto_cmd()
        # Init command.
        self.target.write(json.dumps("Init").encode("ascii"))

        # Write each configuration block to the target.
        self.target.write(json.dumps(core_config).encode("ascii"))
        self.target.write(json.dumps(sensor_config).encode("ascii"))
        self.target.write(json.dumps(alert_config).encode("ascii"))

        device_id = self.target.read_response()
        sensors = self.target.read_response()
        alerts = self.target.read_response()
        owner_page = self.target.read_response()
        boot_log = self.target.read_response()
        boot_measurements = self.target.read_response()
        version = self.target.read_response()
        return (
            device_id,
            sensors,
            alerts,
            owner_page,
            boot_log,
            boot_measurements,
            version,
        )

    def crypto_shadow_reg_access(self) -> None:
        """Starts the crypto.fi.shadow_reg_access test."""
        # CryptoFi command.
        self._ujson_crypto_cmd()
        # ShadowRegAccess command.
        self.target.write(json.dumps("ShadowRegAccess").encode("ascii"))

    def crypto_shadow_reg_read(self) -> None:
        """Starts the crypto.fi.shadow_reg_read test."""
        # CryptoFi command.
        self._ujson_crypto_cmd()
        # ShadowRegRead command.
        self.target.write(json.dumps("ShadowRegRead").encode("ascii"))

    def crypto_aes_key(self, plaintext, key) -> None:
        """Starts the crypto.fi.aes_key test."""
        # CryptoFi command.
        self._ujson_crypto_cmd()
        # Aes command.
        self.target.write(json.dumps("Aes").encode("ascii"))
        # Plaintext and key
        input_data = {"plaintext": plaintext, "key": key}
        self.target.write(json.dumps(input_data).encode("ascii"))
        # Mode payload.
        mode = {
            "key_trigger": True,
            "plaintext_trigger": False,
            "encrypt_trigger": False,
            "ciphertext_trigger": False,
        }
        self.target.write(json.dumps(mode).encode("ascii"))

    def crypto_aes_plaintext(self, plaintext, key) -> None:
        """Starts the crypto.fi.aes_plaintext test."""
        # CryptoFi command.
        self._ujson_crypto_cmd()
        # Aes command.
        self.target.write(json.dumps("Aes").encode("ascii"))
        # Plaintext and key
        input_data = {"plaintext": plaintext, "key": key}
        self.target.write(json.dumps(input_data).encode("ascii"))
        # Mode payload.
        mode = {
            "key_trigger": False,
            "plaintext_trigger": True,
            "encrypt_trigger": False,
            "ciphertext_trigger": False,
        }
        self.target.write(json.dumps(mode).encode("ascii"))

    def crypto_aes_encrypt(self, plaintext, key) -> None:
        """Starts the crypto.fi.aes_encrypt test."""
        # CryptoFi command.
        self._ujson_crypto_cmd()
        # Aes command.
        self.target.write(json.dumps("Aes").encode("ascii"))
        # Plaintext and key
        input_data = {"plaintext": plaintext, "key": key}
        self.target.write(json.dumps(input_data).encode("ascii"))
        # Mode payload.
        mode = {
            "key_trigger": False,
            "plaintext_trigger": False,
            "encrypt_trigger": True,
            "ciphertext_trigger": False,
        }
        self.target.write(json.dumps(mode).encode("ascii"))

    def crypto_aes_ciphertext(self, plaintext, key) -> None:
        """Starts the crypto.fi.aes_ciphertext test."""
        # CryptoFi command.
        self._ujson_crypto_cmd()
        # Aes command.
        self.target.write(json.dumps("Aes").encode("ascii"))
        # Plaintext and key
        input_data = {"plaintext": plaintext, "key": key}
        self.target.write(json.dumps(input_data).encode("ascii"))
        # Mode payload.
        mode = {
            "key_trigger": False,
            "plaintext_trigger": False,
            "encrypt_trigger": False,
            "ciphertext_trigger": True,
        }
        self.target.write(json.dumps(mode).encode("ascii"))

    def crypto_kmac_start(self, plaintext, key) -> None:
        """Starts the crypto.fi.kmac_start test."""
        # CryptoFi command.
        self._ujson_crypto_cmd()
        # Kmac command.
        self.target.write(json.dumps("Kmac").encode("ascii"))
        # Plaintext and key
        input_data = {"plaintext": plaintext, "key": key}
        self.target.write(json.dumps(input_data).encode("ascii"))
        # Mode payload.
        mode = {
            "start_trigger": True,
            "absorb_trigger": False,
            "static_trigger": False,
            "squeeze_trigger": False,
        }
        self.target.write(json.dumps(mode).encode("ascii"))

    def crypto_kmac_absorb(self, plaintext, key) -> None:
        """Starts the crypto.fi.kmac_absorb test."""
        # CryptoFi command.
        self._ujson_crypto_cmd()
        # Kmac command.
        self.target.write(json.dumps("Kmac").encode("ascii"))
        # Plaintext and key
        input_data = {"plaintext": plaintext, "key": key}
        self.target.write(json.dumps(input_data).encode("ascii"))
        # Mode payload.
        mode = {
            "start_trigger": False,
            "absorb_trigger": True,
            "static_trigger": False,
            "squeeze_trigger": False,
        }
        self.target.write(json.dumps(mode).encode("ascii"))

    def crypto_kmac_squeeze(self, plaintext, key) -> None:
        """Starts the crypto.fi.kmac_squeeze test."""
        # CryptoFi command.
        self._ujson_crypto_cmd()
        # Kmac command.
        self.target.write(json.dumps("Kmac").encode("ascii"))
        # Plaintext and key
        input_data = {"plaintext": plaintext, "key": key}
        self.target.write(json.dumps(input_data).encode("ascii"))
        # Mode payload.
        mode = {
            "start_trigger": False,
            "absorb_trigger": False,
            "static_trigger": False,
            "squeeze_trigger": True,
        }
        self.target.write(json.dumps(mode).encode("ascii"))

    def crypto_kmac_static(self, plaintext, key) -> None:
        """Starts the crypto.fi.kmac_static test."""
        # CryptoFi command.
        self._ujson_crypto_cmd()
        # Kmac command.
        self.target.write(json.dumps("Kmac").encode("ascii"))
        # Plaintext and key
        input_data = {"plaintext": plaintext, "key": key}
        self.target.write(json.dumps(input_data).encode("ascii"))
        # Mode payload.
        mode = {
            "start_trigger": False,
            "absorb_trigger": False,
            "static_trigger": True,
            "squeeze_trigger": False,
        }
        self.target.write(json.dumps(mode).encode("ascii"))

    def crypto_kmac_state(self, plaintext, key) -> None:
        """Starts the crypto.fi.kmac_state test."""
        # CryptoFi command.
        self._ujson_crypto_cmd()
        # KmacState command.
        self.target.write(json.dumps("KmacState").encode("ascii"))
        # Plaintext and key
        input_data = {"plaintext": plaintext, "key": key}
        self.target.write(json.dumps(input_data).encode("ascii"))

    def crypto_sha3_start(self, plaintext) -> None:
        """Starts the crypto.fi.sha3_start test."""
        # CryptoFi command.
        self._ujson_crypto_cmd()
        # Sha3 command.
        self.target.write(json.dumps("Sha3").encode("ascii"))
        # Plaintext and key
        input_data = {"plaintext": plaintext}
        self.target.write(json.dumps(input_data).encode("ascii"))
        # Mode payload.
        mode = {
            "start_trigger": True,
            "absorb_trigger": False,
            "static_trigger": False,
            "squeeze_trigger": False,
        }
        self.target.write(json.dumps(mode).encode("ascii"))

    def crypto_sha3_absorb(self, plaintext) -> None:
        """Starts the crypto.fi.sha3_absorb test."""
        # CryptoFi command.
        self._ujson_crypto_cmd()
        # Sha3 command.
        self.target.write(json.dumps("Sha3").encode("ascii"))
        # Plaintext and key
        input_data = {"plaintext": plaintext}
        self.target.write(json.dumps(input_data).encode("ascii"))
        # Mode payload.
        mode = {
            "start_trigger": False,
            "absorb_trigger": True,
            "static_trigger": False,
            "squeeze_trigger": False,
        }
        self.target.write(json.dumps(mode).encode("ascii"))

    def crypto_sha3_static(self, plaintext) -> None:
        """Starts the crypto.fi.sha3_static test."""
        # CryptoFi command.
        self._ujson_crypto_cmd()
        # Sha3 command.
        self.target.write(json.dumps("Sha3").encode("ascii"))
        # Plaintext and key
        input_data = {"plaintext": plaintext}
        self.target.write(json.dumps(input_data).encode("ascii"))
        # Mode payload.
        mode = {
            "start_trigger": False,
            "absorb_trigger": False,
            "static_trigger": True,
            "squeeze_trigger": False,
        }
        self.target.write(json.dumps(mode).encode("ascii"))

    def crypto_sha3_squeeze(self, plaintext) -> None:
        """Starts the crypto.fi.sha3_squeeze test."""
        # CryptoFi command.
        self._ujson_crypto_cmd()
        # Sha3 command.
        self.target.write(json.dumps("Sha3").encode("ascii"))
        # Plaintext and key
        input_data = {"plaintext": plaintext}
        self.target.write(json.dumps(input_data).encode("ascii"))
        # Mode payload.
        mode = {
            "start_trigger": False,
            "absorb_trigger": False,
            "static_trigger": False,
            "squeeze_trigger": True,
        }
        self.target.write(json.dumps(mode).encode("ascii"))

    def crypto_hmac(
        self,
        msg,
        key,
        trigger,
        enable_hmac,
        message_endianness_big,
        digest_endianness_big,
        key_endianness_big,
        hash_mode,
    ) -> None:
        # CryptoFi command.
        self._ujson_crypto_cmd()
        # Sha2 command.
        self.target.write(json.dumps("Hmac").encode("ascii"))
        data = {"message": msg, "key": key}
        self.target.write(json.dumps(data).encode("ascii"))
        if trigger == 0:
            mode = {
                "start_trigger": True,
                "msg_trigger": False,
                "process_trigger": False,
                "finish_trigger": False,
                "enable_hmac": enable_hmac,
                "message_endianness_big": message_endianness_big,
                "digest_endianness_big": digest_endianness_big,
                "key_endianness_big": key_endianness_big,
                "hash_mode": hash_mode,
            }
        elif trigger == 1:
            mode = {
                "start_trigger": False,
                "msg_trigger": True,
                "process_trigger": False,
                "finish_trigger": False,
                "enable_hmac": enable_hmac,
                "message_endianness_big": message_endianness_big,
                "digest_endianness_big": digest_endianness_big,
                "key_endianness_big": key_endianness_big,
                "hash_mode": hash_mode,
            }
        elif trigger == 2:
            mode = {
                "start_trigger": False,
                "msg_trigger": False,
                "process_trigger": True,
                "finish_trigger": False,
                "enable_hmac": enable_hmac,
                "message_endianness_big": message_endianness_big,
                "digest_endianness_big": digest_endianness_big,
                "key_endianness_big": key_endianness_big,
                "hash_mode": hash_mode,
            }
        else:
            mode = {
                "start_trigger": False,
                "msg_trigger": False,
                "process_trigger": False,
                "finish_trigger": True,
                "enable_hmac": enable_hmac,
                "message_endianness_big": message_endianness_big,
                "digest_endianness_big": digest_endianness_big,
                "key_endianness_big": key_endianness_big,
                "hash_mode": hash_mode,
            }
        self.target.write(json.dumps(mode).encode("ascii"))

    def start_test(self, cfg: dict, *args, **kwargs) -> None:
        """ Start the selected test.

        Call the function selected in the config file. Uses the getattr()
        construct to call the function.

        Args:
            cfg: Config dict containing the selected test.
            *args: Variable length argument list to be passed to the test function.
            **kwargs: Arbitrary keyword arguments to be passed to the test function.
        """
        test_function = getattr(self, cfg["test"]["which_test"])
        test_function(*args, **kwargs)
