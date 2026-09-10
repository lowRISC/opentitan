# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Communication interface for OpenTitan Symmetric Cryptolib FI framework.

Communication with OpenTitan happens over the uJSON command interface.
"""
import json
import time
from sw.host.penetrationtests.python.util import common_library


class OTFIAsymCrypto:
    def __init__(self, target) -> None:
        self.target = target

    def _ujson_asym_crypto_fi_cmd(self) -> None:
        self.target.write(json.dumps("CryptoLibFiAsym").encode("ascii"))
        time.sleep(0.003)

    def init(
        self,
        core_config: dict = common_library.default_core_config,
        sensor_config: dict = common_library.default_sensor_config,
        alert_config: dict = common_library.default_alert_config,
    ) -> tuple:
        """Initialize the code on the chip.
        Args:
            cfg: Config dict containing the selected test.

        Returns:
            Device id
            The owner info page
            The boot log
            The boot measurements
            The testOS version
        """

        self._ujson_asym_crypto_fi_cmd()
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
        cryptolib_version = self.target.read_response()
        return (
            device_id,
            sensors,
            alerts,
            owner_page,
            boot_log,
            boot_measurements,
            version,
            cryptolib_version,
        )

    def handle_rsa_enc(
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
        op_enc,
        cfg,
        trigger,
    ) -> None:
        """Call the cryptolib RSA to encrypt/decrypt.

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
            op_enc: Boolean specifying to encrypt or decrypt.
            cfg: Integer for configuration.
            trigger: Integer specifying which triggers to set.
        """
        self._ujson_asym_crypto_fi_cmd()
        self.target.write(json.dumps("RsaEnc").encode("ascii"))
        input_data = {
            "data": data,
            "data_len": data_len,
            "e": e,
            "n": n,
            "n_len": n_len,
            "d": d,
            "padding": padding,
            "hashing": hashing,
            "mode": mode,
            "op_enc": op_enc,
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
        trigger,
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
        self._ujson_asym_crypto_fi_cmd()
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

    def handle_rsa_verify(
        self,
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
    ) -> None:
        """Call the cryptolib RSA to verify.

        Args:
            data: Array of max 512 bytes of input data.
            data_len: Input data length.
            e: Integer for the public e.
            n: Array of max 512 bytes of n.
            n_len: Input n length.
            sig: Array of max 512 bytes of signature data.
            sig_len: Input signature length.
            padding: integer specifying the padding mode.
            hashing: ingteger specifying the hashing mode.
            cfg: Integer for configuration.
            trigger: Integer specifying which triggers to set.
        """
        self._ujson_asym_crypto_fi_cmd()
        self.target.write(json.dumps("RsaVerify").encode("ascii"))
        input_data = {
            "data": data,
            "data_len": data_len,
            "e": e,
            "n": n,
            "n_len": n_len,
            "sig": sig,
            "sig_len": sig_len,
            "padding": padding,
            "hashing": hashing,
            "cfg": cfg,
            "trigger": trigger,
        }
        self.target.write(json.dumps(input_data).encode("ascii"))

    def handle_p256_base_mult(self, scalar, cfg, trigger) -> None:
        """Call the cryptolib p256 base multiplication.

        Args:
            scalar: Array of 32 bytes of scalar data.
            cfg: Integer for configuration.
            trigger: Integer specifying which triggers to set.
        """
        self._ujson_asym_crypto_fi_cmd()
        self.target.write(json.dumps("P256BaseMul").encode("ascii"))
        input_data = {
            "scalar": scalar,
            "cfg": cfg,
            "trigger": trigger,
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
        self._ujson_asym_crypto_fi_cmd()
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
        self._ujson_asym_crypto_fi_cmd()
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
        self._ujson_asym_crypto_fi_cmd()
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

    def handle_p256_verify(self, pubx, puby, r, s, message, cfg, trigger) -> None:
        """Call the cryptolib p256 verify.

        Args:
            pubx: Array of 32 bytes of x-coord data.
            puby: Array of 32 bytes of y-coord data.
            r: Array of 32 bytes of signature data.
            s: Array of 32 bytes of signature data.
            message: Array of 32 bytes of message data.
            cfg: Integer for configuration.
            trigger: Integer specifying which triggers to set.
        """
        self._ujson_asym_crypto_fi_cmd()
        self.target.write(json.dumps("P256Verify").encode("ascii"))
        input_data = {
            "pubx": pubx,
            "puby": puby,
            "r": r,
            "s": s,
            "message": message,
            "cfg": cfg,
            "trigger": trigger,
        }
        self.target.write(json.dumps(input_data).encode("ascii"))

    def handle_p384_base_mult(self, scalar, cfg, trigger) -> None:
        """Call the cryptolib p384 base multiplication.

        Args:
            scalar: Array of 48 bytes of scalar data.
            cfg: Integer for configuration.
            trigger: Integer specifying which triggers to set.
        """
        self._ujson_asym_crypto_fi_cmd()
        self.target.write(json.dumps("P384BaseMul").encode("ascii"))
        input_data = {
            "scalar": scalar,
            "cfg": cfg,
            "trigger": trigger,
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
        self._ujson_asym_crypto_fi_cmd()
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
        self._ujson_asym_crypto_fi_cmd()
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
        self._ujson_asym_crypto_fi_cmd()
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

    def handle_ed25519_sign(self, scalar, message, message_len, cfg, trigger) -> None:
        """Call the cryptolib Ed25519 signing.

        Args:
            scalar: Array of 32 bytes of private key seed data.
            message: Array of max 128 bytes of message data.
            message_len: Length of the message in bytes.
            cfg: Integer for configuration.
            trigger: Integer specifying which triggers to set.
        """
        self._ujson_asym_crypto_fi_cmd()
        self.target.write(json.dumps("Ed25519Sign").encode("ascii"))
        input_data = {
            "scalar": scalar,
            "message": message,
            "message_len": message_len,
            "cfg": cfg,
            "trigger": trigger,
        }
        self.target.write(json.dumps(input_data).encode("ascii"))

    def handle_ed25519_verify(
        self, pubx, puby, r, s, message, message_len, cfg, trigger
    ) -> None:
        """Call the cryptolib Ed25519 verify.

        Args:
            pubx: Array of 32 bytes of compressed public key data.
            puby: Array of 32 bytes (unused for Ed25519, set to zeros).
            r: Array of 64 bytes of signature R data.
            s: Array of 64 bytes of signature S data.
            message: Array of max 128 bytes of message data.
            message_len: Length of the message in bytes.
            cfg: Integer for configuration.
            trigger: Integer specifying which triggers to set.
        """
        self._ujson_asym_crypto_fi_cmd()
        self.target.write(json.dumps("Ed25519Verify").encode("ascii"))
        input_data = {
            "pubx": pubx,
            "puby": puby,
            "r": r,
            "s": s,
            "message": message,
            "message_len": message_len,
            "cfg": cfg,
            "trigger": trigger,
        }
        self.target.write(json.dumps(input_data).encode("ascii"))

    def handle_p384_verify(self, pubx, puby, r, s, message, cfg, trigger) -> None:
        """Call the cryptolib p384 verify.

        Args:
            pubx: Array of 48 bytes of x-coord data.
            puby: Array of 48 bytes of y-coord data.
            r: Array of 48 bytes of signature data.
            s: Array of 48 bytes of signature data.
            message: Array of 32 bytes of message data.
            cfg: Integer for configuration.
            trigger: Integer specifying which triggers to set.
        """
        self._ujson_asym_crypto_fi_cmd()
        self.target.write(json.dumps("P384Verify").encode("ascii"))
        input_data = {
            "pubx": pubx,
            "puby": puby,
            "r": r,
            "s": s,
            "message": message,
            "cfg": cfg,
            "trigger": trigger,
        }
        self.target.write(json.dumps(input_data).encode("ascii"))

    def handle_x25519_base_mult(self, scalar, cfg, trigger) -> None:
        self._ujson_asym_crypto_fi_cmd()
        self.target.write(json.dumps("X25519BaseMul").encode("ascii"))
        input_data = {
            "scalar": scalar,
            "cfg": cfg,
            "trigger": trigger,
        }
        self.target.write(json.dumps(input_data).encode("ascii"))

    def handle_x25519_ecdh(self, private_key, public_x, public_y, cfg, trigger) -> None:
        self._ujson_asym_crypto_fi_cmd()
        self.target.write(json.dumps("X25519Ecdh").encode("ascii"))
        input_data = {
            "private_key": private_key,
            "public_x": public_x,
            "public_y": public_y,
            "cfg": cfg,
            "trigger": trigger,
        }
        self.target.write(json.dumps(input_data).encode("ascii"))

    def handle_mldsa87_keygen(self, seed, cfg, trigger) -> None:
        """Call the cryptolib MLDSA-87 key generation.

        Args:
            seed: Array of 32 bytes of seed data.
            cfg: Integer for configuration.
            trigger: Integer specifying which triggers to set.
        """
        self._ujson_asym_crypto_fi_cmd()
        self.target.write(json.dumps("Mldsa87Keygen").encode("ascii"))
        input_data = {
            "seed": seed,
            "cfg": cfg,
            "trigger": trigger,
        }
        self.target.write(json.dumps(input_data).encode("ascii"))

    def handle_mldsa87_sign(
        self, seed, message, message_len, context, context_len, sign_mode, cfg, trigger
    ) -> None:
        """Call the cryptolib MLDSA-87 signing.

        Args:
            seed: Array of 32 bytes of seed data.
            message: Array of max 128 bytes of message data.
            message_len: Length of the message in bytes.
            context: Array of max 256 bytes of context data.
            context_len: Length of the context in bytes.
            sign_mode: Integer specifying deterministic (1) or randomized (0) mode.
            cfg: Integer for configuration.
            trigger: Integer specifying which triggers to set.
        """
        self._ujson_asym_crypto_fi_cmd()
        self.target.write(json.dumps("Mldsa87Sign").encode("ascii"))
        input_data = {
            "seed": seed,
            "message": message,
            "message_len": message_len,
            "context": context,
            "context_len": context_len,
            "sign_mode": sign_mode,
            "cfg": cfg,
            "trigger": trigger,
        }
        self.target.write(json.dumps(input_data).encode("ascii"))

    def handle_mldsa87_verify(
        self, public_key, message, message_len, context, context_len, signature, cfg, trigger
    ) -> None:
        """Call the cryptolib MLDSA-87 verify.

        Args:
            public_key: Array of 2592 bytes of public key data.
            message: Array of max 128 bytes of message data.
            message_len: Length of the message in bytes.
            context: Array of max 256 bytes of context data.
            context_len: Length of the context in bytes.
            signature: Array of 4628 bytes of signature data.
            cfg: Integer for configuration.
            trigger: Integer specifying which triggers to set.
        """
        self._ujson_asym_crypto_fi_cmd()
        self.target.write(json.dumps("Mldsa87Verify").encode("ascii"))
        input_data = {
            "public_key": public_key,
            "message": message,
            "message_len": message_len,
            "context": context,
            "context_len": context_len,
            "signature": signature,
            "cfg": cfg,
            "trigger": trigger,
        }
        self.target.write(json.dumps(input_data).encode("ascii"))

    def handle_mlkem1024_keygen(self, seed, cfg, trigger) -> None:
        """Call the cryptolib MLKEM-1024 key generation.

        Args:
            seed: Array of 32 bytes of seed data.
            cfg: Integer for configuration.
            trigger: Integer specifying which triggers to set.
        """
        self._ujson_asym_crypto_fi_cmd()
        self.target.write(json.dumps("Mlkem1024Keygen").encode("ascii"))
        input_data = {
            "seed": seed,
            "cfg": cfg,
            "trigger": trigger,
        }
        self.target.write(json.dumps(input_data).encode("ascii"))

    def handle_mlkem1024_encaps(self, public_key, m, cfg, trigger) -> None:
        """Call the cryptolib MLKEM-1024 encapsulation.

        Args:
            public_key: Array of 1568 bytes of public key data.
            m: Array of 32 bytes of randomness data.
            cfg: Integer for configuration.
            trigger: Integer specifying which triggers to set.
        """
        self._ujson_asym_crypto_fi_cmd()
        self.target.write(json.dumps("Mlkem1024Encaps").encode("ascii"))
        input_data = {
            "public_key": public_key,
            "m": m,
            "cfg": cfg,
            "trigger": trigger,
        }
        self.target.write(json.dumps(input_data).encode("ascii"))

    def handle_mlkem1024_decaps(self, ciphertext, cfg, trigger) -> None:
        """Call the cryptolib MLKEM-1024 decapsulation.

        Args:
            ciphertext: Array of 1568 bytes of ciphertext data.
            cfg: Integer for configuration.
            trigger: Integer specifying which triggers to set.
        """
        self._ujson_asym_crypto_fi_cmd()
        self.target.write(json.dumps("Mlkem1024Decaps").encode("ascii"))
        input_data = {
            "ciphertext": ciphertext,
            "cfg": cfg,
            "trigger": trigger,
        }
        self.target.write(json.dumps(input_data).encode("ascii"))
