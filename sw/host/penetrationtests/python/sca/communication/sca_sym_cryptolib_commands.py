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


class OTSymCrypto:
    def __init__(self, target) -> None:
        self.target = target

    def _ujson_sym_crypto_sca_cmd(self):
        self.target.write(json.dumps("CryptoLibScaSym").encode("ascii"))
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
        self._ujson_sym_crypto_sca_cmd()
        self.target.write(json.dumps("Init").encode("ascii"))

        # Write each configuration block to the target.
        self.target.write(json.dumps(core_config).encode("ascii"))
        self.target.write(json.dumps(sensor_config).encode("ascii"))

        device_id = self.target.read_response()
        owner_page = self.target.read_response()
        boot_log = self.target.read_response()
        boot_measurements = self.target.read_response()
        version = self.target.read_response()
        cryptolib_version = self.target.read_response()
        return (
            device_id,
            owner_page,
            boot_log,
            boot_measurements,
            version,
            cryptolib_version,
        )

    def handle_aes_fvsr_plaintext(
        self,
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
    ) -> None:
        """Call the cryptolib AES.

        Args:
            data: Array of max 64 bytes of input data.
            data_len: Input data length.
            key: Array of max 32 bytes of key data.
            key_len: Input key length.
            iv: Array of 16 bytes for the iv.
            padding: integer specifying the padding mode.
            mode: integer specifying the mode of operations.
            op_enc: Boolean specifying to encrypt or decrypt.
            cfg: Integer for configuration.
            trigger: Integer specifying which triggers to set.
            num_iterations: Number of segments in the batching.
        """
        self._ujson_sym_crypto_sca_cmd()
        self.target.write(json.dumps("AesFvsrPlaintext").encode("ascii"))
        input_data = {
            "data": data,
            "data_len": data_len,
            "key": key,
            "key_len": key_len,
            "iv": iv,
            "padding": padding,
            "mode": mode,
            "op_enc": op_enc,
            "cfg": cfg,
            "trigger": trigger,
            "num_iterations": num_iterations,
        }
        self.target.write(json.dumps(input_data).encode("ascii"))

    def handle_aes_daisy(
        self,
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
    ) -> None:
        """Call the cryptolib AES.

        Args:
            data: Array of max 64 bytes of input data.
            data_len: Input data length.
            key: Array of max 32 bytes of key data.
            key_len: Input key length.
            iv: Array of 16 bytes for the iv.
            padding: integer specifying the padding mode.
            mode: integer specifying the mode of operations.
            op_enc: Boolean specifying to encrypt or decrypt.
            cfg: Integer for configuration.
            trigger: Integer specifying which triggers to set.
            num_iterations: Number of segments in the batching.
        """
        self._ujson_sym_crypto_sca_cmd()
        self.target.write(json.dumps("AesDaisy").encode("ascii"))
        input_data = {
            "data": data,
            "data_len": data_len,
            "key": key,
            "key_len": key_len,
            "iv": iv,
            "padding": padding,
            "mode": mode,
            "op_enc": op_enc,
            "cfg": cfg,
            "trigger": trigger,
            "num_iterations": num_iterations,
        }
        self.target.write(json.dumps(input_data).encode("ascii"))

    def handle_cmac_fvsr_plaintext(
        self, data, data_len, key, key_len, iv, cfg, trigger, num_iterations
    ) -> None:
        """Call the cryptolib CMAC.

        Args:
            data: Array of max 64 bytes of input data.
            data_len: Input data length.
            key: Array of max 32 bytes of key data.
            key_len: Input key length.
            iv: Array of 16 bytes for the iv.
            cfg: Integer for configuration.
            trigger: Integer specifying which triggers to set.
            num_iterations: Number of segments in the batching.
        """
        self._ujson_sym_crypto_sca_cmd()
        self.target.write(json.dumps("CmacFvsrPlaintext").encode("ascii"))
        input_data = {
            "data": data,
            "data_len": data_len,
            "key": key,
            "key_len": key_len,
            "iv": iv,
            "cfg": cfg,
            "trigger": trigger,
            "num_iterations": num_iterations,
        }
        self.target.write(json.dumps(input_data).encode("ascii"))

    def handle_cmac_daisy(
        self, data, data_len, key, key_len, iv, cfg, trigger, num_iterations
    ) -> None:
        """Call the cryptolib CMAC.

        Args:
            data: Array of max 64 bytes of input data.
            data_len: Input data length.
            key: Array of max 32 bytes of key data.
            key_len: Input key length.
            iv: Array of 16 bytes for the iv.
            cfg: Integer for configuration.
            trigger: Integer specifying which triggers to set.
            num_iterations: Number of segments in the batching.
        """
        self._ujson_sym_crypto_sca_cmd()
        self.target.write(json.dumps("CmacDaisy").encode("ascii"))
        input_data = {
            "data": data,
            "data_len": data_len,
            "key": key,
            "key_len": key_len,
            "iv": iv,
            "cfg": cfg,
            "trigger": trigger,
            "num_iterations": num_iterations,
        }
        self.target.write(json.dumps(input_data).encode("ascii"))

    def handle_gcm_fvsr_plaintext(
        self,
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
    ) -> None:
        """Call the cryptolib GCM.

        Args:
            data: Array of max 64 bytes of input data.
            data_len: Input data length.
            key: Array of max 32 bytes of key data.
            key_len: Input key length.
            aad: Array of max 64 bytes of aad data.
            aad_len: Input aad length.
            iv: Array of 16 bytes for the iv.
            cfg: Integer for configuration.
            trigger: Integer specifying which triggers to set.
            num_iterations: Number of segments in the batching.
        """
        self._ujson_sym_crypto_sca_cmd()
        self.target.write(json.dumps("GcmFvsrPlaintext").encode("ascii"))
        input_data = {
            "data": data,
            "data_len": data_len,
            "key": key,
            "key_len": key_len,
            "aad": aad,
            "aad_len": aad_len,
            "iv": iv,
            "cfg": cfg,
            "trigger": trigger,
            "num_iterations": num_iterations,
        }
        self.target.write(json.dumps(input_data).encode("ascii"))

    def handle_gcm_daisy(
        self,
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
    ) -> None:
        """Call the cryptolib GCM.

        Args:
            data: Array of max 64 bytes of input data.
            data_len: Input data length.
            key: Array of max 32 bytes of key data.
            key_len: Input key length.
            aad: Array of max 64 bytes of aad data.
            aad_len: Input aad length.
            iv: Array of 16 bytes for the iv.
            cfg: Integer for configuration.
            trigger: Integer specifying which triggers to set.
            num_iterations: Number of segments in the batching.
        """
        self._ujson_sym_crypto_sca_cmd()
        self.target.write(json.dumps("GcmDaisy").encode("ascii"))
        input_data = {
            "data": data,
            "data_len": data_len,
            "key": key,
            "key_len": key_len,
            "aad": aad,
            "aad_len": aad_len,
            "iv": iv,
            "cfg": cfg,
            "trigger": trigger,
            "num_iterations": num_iterations,
        }
        self.target.write(json.dumps(input_data).encode("ascii"))

    def handle_hmac_fvsr_plaintext(
        self, data, data_len, key, key_len, hash_mode, mode, cfg, trigger, num_iterations
    ) -> None:
        """Call the cryptolib HMAC.

        Args:
            data: Array of max 64 bytes of input data.
            data_len: Input data length.
            key: Array of max 192 bytes of key data.
            key_len: Input key length.
            hash_mode: integer specifying the hash mode.
            mode: integer specifying the mode of operations.
            cfg: Integer for configuration.
            trigger: Integer specifying which triggers to set.
            num_iterations: Number of segments in the batching.
        """
        self._ujson_sym_crypto_sca_cmd()
        self.target.write(json.dumps("HmacFvsrPlaintext").encode("ascii"))
        input_data = {
            "data": data,
            "data_len": data_len,
            "key": key,
            "key_len": key_len,
            "hash_mode": hash_mode,
            "mode": mode,
            "cfg": cfg,
            "trigger": trigger,
            "num_iterations": num_iterations,
        }
        self.target.write(json.dumps(input_data).encode("ascii"))

    def handle_hmac_daisy(
        self, data, data_len, key, key_len, hash_mode, mode, cfg, trigger, num_iterations
    ) -> None:
        """Call the cryptolib HMAC.

        Args:
            data: Array of max 64 bytes of input data.
            data_len: Input data length.
            key: Array of max 192 bytes of key data.
            key_len: Input key length.
            hash_mode: integer specifying the hash mode.
            mode: integer specifying the mode of operations.
            cfg: Integer for configuration.
            trigger: Integer specifying which triggers to set.
            num_iterations: Number of segments in the batching.
        """
        self._ujson_sym_crypto_sca_cmd()
        self.target.write(json.dumps("HmacDaisy").encode("ascii"))
        input_data = {
            "data": data,
            "data_len": data_len,
            "key": key,
            "key_len": key_len,
            "hash_mode": hash_mode,
            "mode": mode,
            "cfg": cfg,
            "trigger": trigger,
            "num_iterations": num_iterations,
        }
        self.target.write(json.dumps(input_data).encode("ascii"))

    def handle_drbg_reseed(
        self,
        entropy,
        entropy_len,
        nonce,
        nonce_len,
        reseed_interval,
        mode,
        cfg,
        trigger,
    ) -> None:
        """Call the cryptolib DRBG to reseed.

        Args:
            entropy: Array of max 32 bytes of entropy data.
            entropy_len: Input entropy length.
            nonce: Array of max 16 bytes of nonce data.
            nonce_len: Input nonce length.
            reseed_interval: when to reseed.
            mode: integer specifying the mode.
            cfg: Integer for configuration.
            trigger: Integer specifying which triggers to set.
        """
        self._ujson_sym_crypto_sca_cmd()
        self.target.write(json.dumps("DrbgReseed").encode("ascii"))
        input_data = {
            "entropy": entropy,
            "entropy_len": entropy_len,
            "nonce": nonce,
            "nonce_len": nonce_len,
            "reseed_interval": reseed_interval,
            "mode": mode,
            "cfg": cfg,
            "trigger": trigger,
        }
        self.target.write(json.dumps(input_data).encode("ascii"))

    def handle_drbg_generate(
        self, nonce, nonce_len, data_len, mode, cfg, trigger, num_iterations
    ) -> None:
        """Call the cryptolib DRBG to generate randomness.

        Args:
            nonce: Array of max 16 bytes of nonce data.
            nonce_len: Input nonce length.
            data_len: Length of the output data.
            reseed_interval: when to reseed.
            mode: integer specifying the mode.
            cfg: Integer for configuration.
            trigger: Integer specifying which triggers to set.
            num_iterations: Number of segments in the batching.
        """
        self._ujson_sym_crypto_sca_cmd()
        self.target.write(json.dumps("DrbgGenerateBatch").encode("ascii"))
        input_data = {
            "nonce": nonce,
            "nonce_len": nonce_len,
            "data_len": data_len,
            "mode": mode,
            "cfg": cfg,
            "trigger": trigger,
            "num_iterations": num_iterations,
        }
        self.target.write(json.dumps(input_data).encode("ascii"))
