# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Communication interface for the SHA3 SCA application on OpenTitan.

Communication with OpenTitan happens over the uJson
command interface.
"""
import json
import time
from sw.host.penetrationtests.python.util import common_library


class OTAsymCrypto:
    def __init__(self, target) -> None:
        self.target = target

    def _ujson_asym_crypto_sca_cmd(self):
        self.target.write(json.dumps("CryptoLibScaAsym").encode("ascii"))
        time.sleep(0.003)

    def init(
        self,
        core_config: dict = common_library.default_core_config,
        sensor_config: dict = common_library.default_sensor_config,
    ) -> tuple:
        """Initializes Sym Cryptolib on the target.

        Returns:
            Device id
            The owner info page
            The boot log
            The boot measurements
            The testOS version
        """
        self._ujson_asym_crypto_sca_cmd()
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

    def handle_rsa_dec(
        self,
        data,
        data_len,
        e,
        n,
        n_len,
        d,
        padding,
        hashing,
        mode,
        cfg,
        trigger,
    ) -> None:
        """Call the cryptolib RSA.

        Args:
            data: Array of max 512 bytes of input data.
            data_len: Input data length.
            e: Integer for the public e.
            n: Array of max 512 bytes of n.
            n_len: Input n length.
            d: Array of max 512 bytes of d.
            padding: integer specifying the padding mode.
            hashing: ingteger specifying the hashing mode.
            mode: integer specifying the mode.
            cfg: Integer for configuration.
            trigger: Integer specifying which triggers to set.
        """
        self._ujson_asym_crypto_sca_cmd()
        self.target.write(json.dumps("RsaDec").encode("ascii"))
        input_data = {
            "data": data,
            "data_len": data_len,
            "mode": mode,
            "e": e,
            "n": n,
            "d": d,
            "n_len": n_len,
            "hashing": hashing,
            "padding": padding,
            "cfg": cfg,
            "trigger": trigger,
        }
        self.target.write(json.dumps(input_data).encode("ascii"))

    def handle_rsa_sign(
        self,
        data,
        data_len,
        e,
        n,
        n_len,
        d,
        padding,
        hashing,
        cfg,
        trigger
    ) -> None:
        """Call the cryptolib RSA to sign.

        Args:
            data: Array of max 512 bytes of input data.
            data_len: Input data length.
            e: Integer for the public e.
            n: Array of max 512 bytes of n.
            n_len: Input n length.
            d: Array of max 512 bytes of d.
            padding: integer specifying the padding mode.
            hashing: ingteger specifying the hashing mode.
            cfg: Integer for configuration.
            trigger: Integer specifying which triggers to set.
        """
        self._ujson_asym_crypto_sca_cmd()
        self.target.write(json.dumps("RsaSign").encode("ascii"))
        input_data = {
            "data": data,
            "data_len": data_len,
            "e": e,
            "n": n,
            "n_len": n_len,
            "d": d,
            "padding": padding,
            "hashing": hashing,
            "cfg": cfg,
            "trigger": trigger,
        }
        self.target.write(json.dumps(input_data).encode("ascii"))

    def handle_prime_generation(self, e, cfg, trigger) -> None:
        """Call the cryptolib to generate prime numbers.

        Args:
            e: Integer for the public e.
            cfg: Integer for configuration.
            trigger: Integer specifying which triggers to set.
        """
        self._ujson_asym_crypto_sca_cmd()
        self.target.write(json.dumps("Prime").encode("ascii"))
        input_data = {
            "e": e,
            "cfg": cfg,
            "trigger": trigger,
        }
        self.target.write(json.dumps(input_data).encode("ascii"))

    def handle_p256_base_mult_fvsr(self, scalar, cfg, trigger, num_iterations) -> None:
        """Call the cryptolib p256 base multiplication.

        Args:
            scalar: Array of 32 bytes of scalar data.
            cfg: Integer for configuration.
            trigger: Integer specifying which triggers to set.
            num_iterations: Number of segments in the batching.
        """
        self._ujson_asym_crypto_sca_cmd()
        self.target.write(json.dumps("P256BaseMulFvsr").encode("ascii"))
        input_data = {
            "scalar": scalar,
            "cfg": cfg,
            "trigger": trigger,
            "num_iterations": num_iterations
        }
        self.target.write(json.dumps(input_data).encode("ascii"))

    def handle_p256_base_mult_daisy(self, scalar, cfg, trigger, num_iterations) -> None:
        """Call the cryptolib p256 base multiplication.

        Args:
            scalar: Array of 32 bytes of scalar data.
            cfg: Integer for configuration.
            trigger: Integer specifying which triggers to set.
            num_iterations: Number of segments in the batching.
        """
        self._ujson_asym_crypto_sca_cmd()
        self.target.write(json.dumps("P256BaseMulDaisy").encode("ascii"))
        input_data = {
            "scalar": scalar,
            "cfg": cfg,
            "trigger": trigger,
            "num_iterations": num_iterations
        }
        self.target.write(json.dumps(input_data).encode("ascii"))

    def handle_p256_point_mult(self, scalar_alice, scalar_bob, cfg, trigger) -> None:
        """Call the cryptolib p256 point multiplication.

        Args:
            scalar_alice: Array of 32 bytes of scalar data.
            scalar_bob: Array of 32 bytes of scalar data.
            cfg: Integer for configuration.
            trigger: Integer specifying which triggers to set.
        """
        self._ujson_asym_crypto_sca_cmd()
        self.target.write(json.dumps("P256PointMul").encode("ascii"))
        input_data = {
            "scalar_alice": scalar_alice,
            "scalar_bob": scalar_bob,
            "cfg": cfg,
            "trigger": trigger,
        }
        self.target.write(json.dumps(input_data).encode("ascii"))

    def handle_p256_ecdh(self, private_key, public_x, public_y, cfg, trigger) -> None:
        """Call the cryptolib p256 ecdh.

        Args:
            private_key: Array of 32 bytes of scalar data.
            public_x: Array of 32 bytes of x-coord data.
            public_y: Array of 32 bytes of y-coord data.
            cfg: Integer for configuration.
            trigger: Integer specifying which triggers to set.
        """
        self._ujson_asym_crypto_sca_cmd()
        self.target.write(json.dumps("P256Ecdh").encode("ascii"))
        input_data = {
            "private_key": private_key,
            "public_x": public_x,
            "public_y": public_y,
            "cfg": cfg,
            "trigger": trigger,
        }
        self.target.write(json.dumps(input_data).encode("ascii"))

    def handle_p256_sign(self, scalar, pubx, puby, message, cfg, trigger) -> None:
        """Call the cryptolib p256 signing.

        Args:
            scalar: Array of 32 bytes of scalar data.
            pubx: Array of 32 bytes of x-coord data.
            puby: Array of 32 bytes of y-coord data.
            message: Array of 32 bytes of message data.
            cfg: Integer for configuration.
            trigger: Integer specifying which triggers to set.
        """
        self._ujson_asym_crypto_sca_cmd()
        self.target.write(json.dumps("P256Sign").encode("ascii"))
        input_data = {
            "scalar": scalar,
            "pubx": pubx,
            "puby": puby,
            "message": message,
            "cfg": cfg,
            "trigger": trigger,
        }
        self.target.write(json.dumps(input_data).encode("ascii"))

    def handle_p384_base_mult_fvsr(self, scalar, cfg, trigger, num_iterations) -> None:
        """Call the cryptolib p384 base multiplication.

        Args:
            scalar: Array of 48 bytes of scalar data.
            cfg: Integer for configuration.
            trigger: Integer specifying which triggers to set.
            num_iterations: Number of segments in the batching.
        """
        self._ujson_asym_crypto_sca_cmd()
        self.target.write(json.dumps("P384BaseMulFvsr").encode("ascii"))
        input_data = {
            "scalar": scalar,
            "cfg": cfg,
            "trigger": trigger,
            "num_iterations": num_iterations
        }
        self.target.write(json.dumps(input_data).encode("ascii"))

    def handle_p384_base_mult_daisy(self, scalar, cfg, trigger, num_iterations) -> None:
        """Call the cryptolib p384 base multiplication.

        Args:
            scalar: Array of 48 bytes of scalar data.
            cfg: Integer for configuration.
            trigger: Integer specifying which triggers to set.
            num_iterations: Number of segments in the batching.
        """
        self._ujson_asym_crypto_sca_cmd()
        self.target.write(json.dumps("P384BaseMulDaisy").encode("ascii"))
        input_data = {
            "scalar": scalar,
            "cfg": cfg,
            "trigger": trigger,
            "num_iterations": num_iterations
        }
        self.target.write(json.dumps(input_data).encode("ascii"))

    def handle_p384_point_mult(self, scalar_alice, scalar_bob, cfg, trigger) -> None:
        """Call the cryptolib p384 point multiplication.

        Args:
            scalar_alice: Array of 48 bytes of scalar data.
            scalar_bob: Array of 48 bytes of scalar data.
            cfg: Integer for configuration.
            trigger: Integer specifying which triggers to set.
        """
        self._ujson_asym_crypto_sca_cmd()
        self.target.write(json.dumps("P384PointMul").encode("ascii"))
        input_data = {
            "scalar_alice": scalar_alice,
            "scalar_bob": scalar_bob,
            "cfg": cfg,
            "trigger": trigger,
        }
        self.target.write(json.dumps(input_data).encode("ascii"))

    def handle_p384_ecdh(self, private_key, public_x, public_y, cfg, trigger) -> None:
        """Call the cryptolib p384 ecdh.

        Args:
            private_key: Array of 48 bytes of scalar data.
            public_x: Array of 48 bytes of x-coord data.
            public_y: Array of 48 bytes of y-coord data.
            cfg: Integer for configuration.
            trigger: Integer specifying which triggers to set.
        """
        self._ujson_asym_crypto_sca_cmd()
        self.target.write(json.dumps("P384Ecdh").encode("ascii"))
        input_data = {
            "private_key": private_key,
            "public_x": public_x,
            "public_y": public_y,
            "cfg": cfg,
            "trigger": trigger,
        }
        self.target.write(json.dumps(input_data).encode("ascii"))

    def handle_p384_sign(self, scalar, pubx, puby, message, cfg, trigger) -> None:
        """Call the cryptolib p384 signing.

        Args:
            scalar: Array of 48 bytes of scalar data.
            pubx: Array of 48 bytes of x-coord data.
            puby: Array of 48 bytes of y-coord data.
            message: Array of 48 bytes of message data.
            cfg: Integer for configuration.
            trigger: Integer specifying which triggers to set.
        """
        self._ujson_asym_crypto_sca_cmd()
        self.target.write(json.dumps("P384Sign").encode("ascii"))
        input_data = {
            "scalar": scalar,
            "pubx": pubx,
            "puby": puby,
            "message": message,
            "cfg": cfg,
            "trigger": trigger,
        }
        self.target.write(json.dumps(input_data).encode("ascii"))
