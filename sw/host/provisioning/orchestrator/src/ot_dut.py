# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import logging
import os
from dataclasses import dataclass

from device_id import DeviceId
from sku_config import SkuConfig
from util import confirm, format_hex, run

# FPGA bitstream.
_FPGA_UNIVERSAL_SPLICE_BITSTREAM = "hw/bitstream/universal/splice.bit"

# CP and FT shared flags.
_BASE_PROVISIONING_FLAGS = """
    --interface={} \
    --openocd=third_party/openocd/build_openocd/bin/openocd \
    --openocd-adapter-config=external/openocd/tcl/interface/cmsis-dap.cfg \
"""
_ZERO_256BIT_HEXSTR = "0x" + "_".join(["00000000"] * 8)

# yapf: disable
# CP & FT Device Firmware
_BASE_DEV_DIR          = "sw/device/silicon_creator/manuf/base"  # noqa: E221
_CP_DEVICE_ELF         = _BASE_DEV_DIR + "/sram_cp_provision_{}.elf"  # noqa: E221
_FT_INDIVID_DEVICE_ELF = _BASE_DEV_DIR + "/sram_ft_individualize_{}_{}.elf"  # noqa: E221
_FT_PERSO_DEVICE_BIN   = _BASE_DEV_DIR + "/ft_personalize_{}_{}.prod_key_0.prod_key_0.signed.bin"  # noqa: E221, E501
_FT_FW_BUNDLE_BIN      = _BASE_DEV_DIR + "/ft_fw_bundle_{}_{}.img"  # noqa: E221
# CP & FT Host Binaries
_CP_HOST_BIN = "sw/host/provisioning/cp/cp"
_FT_HOST_BIN = "sw/host/provisioning/ft/ft_{}"
# yapf: enable


@dataclass
class OtDut():
    """Class for holding data and routines for running provisioning flows."""
    logs_root_dir: str
    sku_config: SkuConfig
    device_id: DeviceId
    test_unlock_token: str
    test_exit_token: str
    rma_unlock_token: str
    fpga: str
    require_confirmation: bool = True

    def __post_init__(self):
        self.log_dir = f"{self.logs_root_dir}/{str(self.device_id)[2:]}"
        self._make_log_dir()

    def _make_log_dir(self) -> None:
        if self.require_confirmation and os.path.exists(self.log_dir):
            logging.warning(
                f"Log file {self.log_dir} already exists. Continue to overwrite."
            )
            confirm()
        os.makedirs(self.log_dir, exist_ok=True)

    def run_cp(self) -> None:
        """Runs the CP provisioning flow on the target DUT."""
        logging.info("Running CP provisioning ...")

        # Set cmd args and device ELF.
        host_flags = _BASE_PROVISIONING_FLAGS
        device_elf = _CP_DEVICE_ELF
        if self.fpga:
            # Set host flags and device binary for FPGA DUT.
            host_flags = host_flags.format(self.fpga)
            host_flags += " --clear-bitstream"
            host_flags += f" --bitstream={_FPGA_UNIVERSAL_SPLICE_BITSTREAM}"
            device_elf = device_elf.format(
                f"fpga_{self.fpga}_rom_with_fake_keys")
        else:
            # Set host flags and device binary for Silicon DUT.
            host_flags = host_flags.format("teacup")
            host_flags += " --disable-dft-on-reset"
            device_elf = device_elf.format("silicon_creator")

        # Assemble CP command.
        cmd = f"""{_CP_HOST_BIN} \
        --rcfile= \
        --logging=info \
        {host_flags} \
        --elf={device_elf} \
        --device-id="{self.device_id}" \
        --test-unlock-token="{format_hex(self.test_unlock_token, width=32)}" \
        --test-exit-token="{format_hex(self.test_exit_token, width=32)}" \
        --manuf-state="{_ZERO_256BIT_HEXSTR}" \
        --wafer-auth-secret="{_ZERO_256BIT_HEXSTR}" \
        """

        # TODO: capture DIN portion of device ID and update device ID.

        # Get user confirmation before running command.
        logging.info(f"Running command: {cmd}")
        if self.require_confirmation:
            confirm()

        # Run provisioning flow and collect logs.
        res = run(cmd, f"{self.log_dir}/cp_out.log.txt",
                  f"{self.log_dir}/cp_err.log.txt")
        if res.returncode != 0:
            logging.warning(f"CP failed with exit code: {res.returncode}.")
            confirm()
        else:
            logging.info("CP completed successfully.")

    def run_ft(self) -> None:
        """Runs the FT provisioning flow on the target DUT."""
        logging.info("Running FT provisioning ...")

        # Set cmd args and device ELF.
        host_bin = _FT_HOST_BIN.format(self.sku_config.name)
        host_flags = _BASE_PROVISIONING_FLAGS
        individ_elf = _FT_INDIVID_DEVICE_ELF
        perso_bin = _FT_PERSO_DEVICE_BIN
        fw_bundle_bin = _FT_FW_BUNDLE_BIN
        if self.fpga:
            # Set host flags and device binaries for FPGA DUT.
            # No need to load another bitstream, we will take over where CP
            # stage above left off.
            host_flags = host_flags.format(self.fpga)
            individ_elf = individ_elf.format(
                self.sku_config.name, f"fpga_{self.fpga}_rom_with_fake_keys")
            perso_bin = perso_bin.format(
                self.sku_config.name, f"fpga_{self.fpga}_rom_with_fake_keys")
            fw_bundle_bin = fw_bundle_bin.format(
                self.sku_config.name, f"fpga_{self.fpga}_rom_with_fake_keys")
        else:
            # Set host flags and device binaries for Silicon DUT.
            host_flags = host_flags.format("teacup")
            host_flags += " --disable-dft-on-reset"
            individ_elf = individ_elf.format(self.sku_config.name,
                                             "silicon_creator")
            perso_bin = perso_bin.format(self.sku_config.name,
                                         "silicon_creator")
            fw_bundle_bin = fw_bundle_bin.format(self.sku_config.name,
                                                 "silicon_creator")

        # Assemble bazel command.
        # TODO: support multiple CAs
        # TODO: support cloud KMS CAs
        # TODO: autocompute measurements of expected ROM_EXT + Owner FW payloads
        # TODO: add expected ROM_EXT / Owner security versions
        cmd = f"""{host_bin}
        --rcfile= \
        --logging=info \
        {host_flags} \
        --elf={individ_elf} \
        --bootstrap={perso_bin} \
        --second-bootstrap={fw_bundle_bin} \
        --device-id="{self.device_id}" \
        --test-unlock-token="{format_hex(self.test_unlock_token, width=32)}" \
        --test-exit-token="{format_hex(self.test_exit_token, width=32)}" \
        --rma-unlock-token="{format_hex(self.rma_unlock_token, width=32)}" \
        --target-mission-mode-lc-state="{self.sku_config.target_lc_state}" \
        --rom-ext-measurement="{_ZERO_256BIT_HEXSTR}" \
        --owner-manifest-measurement="{_ZERO_256BIT_HEXSTR}" \
        --owner-measurement="{_ZERO_256BIT_HEXSTR}" \
        --rom-ext-security-version="0" \
        --owner-security-version="0" \
        --ca-key-der-file={self.sku_config.dice_ca.key} \
        --ca-key-id={self.sku_config.dice_ca.key_id} \
        --ca-certificate={self.sku_config.dice_ca.certificate} \
        """

        # Get user confirmation before running command.
        logging.info(f"Running command: {cmd}")
        if self.require_confirmation:
            confirm()

        # Run provisioning flow and collect logs.
        res = run(cmd, f"{self.log_dir}/ft_out.log.txt",
                  f"{self.log_dir}/ft_err.log.txt")
        if res.returncode != 0:
            logging.warning(f"FT failed with exit code: {res.returncode}.")
            confirm()
        else:
            logging.info("FT completed successfully.")
