# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import json
import logging
import os
import re
import shutil
import tempfile
from dataclasses import dataclass

import hjson

from device_id import DeviceId, DeviceIdentificationNumber
from sku_config import SkuConfig
from util import confirm, format_hex, run

# FPGA bitstream.
_FPGA_UNIVERSAL_SPLICE_BITSTREAM = "hw/bitstream/universal/splice.bit"

# CP and FT shared flags.
_OPENOCD_BIN = "third_party/openocd/build_openocd/bin/openocd"
_OPENOCD_ADAPTER_CONFIG = "external/openocd/tcl/interface/cmsis-dap.cfg"
_BASE_PROVISIONING_FLAGS = """
    --interface={target} \
    --openocd={openocd_bin} \
    --openocd-adapter-config={openocd_cfg} \
"""
_ZERO_256BIT_HEXSTR = "0x" + "_".join(["00000000"] * 8)

# yapf: disable
# CP & FT Device Firmware
_BASE_DEV_DIR           = "sw/device/silicon_creator/manuf/base"  # noqa: E221
_CP_DEVICE_ELF          = "{base_dir}/sram_cp_provision_{target}.elf"  # noqa: E221
_FT_INDIVID_DEVICE_ELF  = "{base_dir}/sram_ft_individualize_{otp}_{target}.elf"  # noqa: E221
_FT_FW_BUNDLE_BIN       = "{base_dir}/ft_fw_bundle_{sku}_{target}.img"  # noqa: E221
# CP & FT Host Binaries
_CP_HOST_BIN = "sw/host/provisioning/cp/cp"
_FT_HOST_BIN = "sw/host/provisioning/ft/ft_{sku}"
# yapf: enable


@dataclass
class OtDut():
    """Class for holding data and routines for running provisioning flows."""
    logs_root_dir: str
    sku_config: SkuConfig
    device_id: DeviceId
    test_unlock_token: str
    test_exit_token: str
    fpga: str
    require_confirmation: bool = True

    def _make_log_dir(self) -> None:
        self.log_dir = f"{self.logs_root_dir}/{str(self.device_id)[2:]}"
        if self.require_confirmation and os.path.exists(self.log_dir):
            logging.warning(
                f"Log file {self.log_dir} already exists. Continue to overwrite."
            )
            confirm()
        os.makedirs(self.log_dir, exist_ok=True)

    def _extract_json_data(self, key: str, log_file: str) -> dict:
        """Extracts and logs JSON data from a log file.

        Args:
            key: The key to search for in the log file.
            log_file: The log file to search in.
        Retuns:
            The extracted JSON data.
        """
        with open(log_file, "r") as f:
            log_data = f.read()

        pattern = key + r':\s*({.*})'
        match = re.search(pattern, log_data)
        if match:
            json_string = match.group(1)
            try:
                json_data = hjson.loads(json_string)
            except hjson.HjsonDecodeError as e:
                logging.error(f"Failed to parse {key}: {e}")
                confirm()
        else:
            logging.error(f"{key} not found.")
            confirm()
        return json_data

    def _base_dev_dir(self) -> str:
        return _BASE_DEV_DIR

    def run_cp(self) -> None:
        """Runs the CP provisioning flow on the target DUT."""
        logging.info("Running CP provisioning ...")

        # Set cmd args and device ELF.
        host_flags = _BASE_PROVISIONING_FLAGS
        device_elf = _CP_DEVICE_ELF
        print(f"device_elf: {device_elf}")
        if self.fpga:
            # Set host flags and device binary for FPGA DUT.
            host_flags = host_flags.format(target=self.fpga,
                                           openocd_bin=_OPENOCD_BIN,
                                           openocd_cfg=_OPENOCD_ADAPTER_CONFIG)
            host_flags += " --clear-bitstream"
            host_flags += f" --bitstream={_FPGA_UNIVERSAL_SPLICE_BITSTREAM}"
            device_elf = device_elf.format(
                base_dir=self._base_dev_dir(),
                target=f"fpga_{self.fpga}_rom_with_fake_keys")
        else:
            # Set host flags and device binary for Silicon DUT.
            host_flags = host_flags.format(target="teacup",
                                           openocd_bin=_OPENOCD_BIN,
                                           openocd_cfg=_OPENOCD_ADAPTER_CONFIG)
            host_flags += " --disable-dft-on-reset"
            device_elf = device_elf.format(base_dir=self._base_dev_dir(),
                                           target="silicon_creator")

        # Assemble CP command.
        cmd = f"""{_CP_HOST_BIN} \
        --rcfile= \
        --logging=info \
        {host_flags} \
        --elf={device_elf} \
        --test-unlock-token="{format_hex(self.test_unlock_token, width=32)}" \
        --test-exit-token="{format_hex(self.test_exit_token, width=32)}" \
        --wafer-auth-secret="{_ZERO_256BIT_HEXSTR}" \
        """

        # Get user confirmation before running command.
        logging.info(f"Running command: {cmd}")
        if self.require_confirmation:
            confirm()

        # Run provisioning flow and collect logs.
        with tempfile.TemporaryDirectory() as tmpdir:
            stdout_logfile = f"{tmpdir}/cp_out.log.txt"
            stderr_logfile = f"{tmpdir}/cp_err.log.txt"
            res = run(cmd, stdout_logfile, stderr_logfile)

            if res.returncode != 0:
                logging.warning(f"CP failed with exit code: {res.returncode}.")
                confirm()

            # Extract CP device ID.
            chip_probe_data = self._extract_json_data("CHIP_PROBE_DATA",
                                                      stdout_logfile)
            din_from_device = None
            if "cp_device_id" not in chip_probe_data:
                logging.error("cp_device_id not found in CHIP_PROBE_DATA.")
                confirm()
            else:
                if chip_probe_data["cp_device_id"] == "":
                    logging.warning(
                        "cp_device_id empty; setting default of all zeros.")
                    din_from_device = DeviceIdentificationNumber(0)
                else:
                    din_from_device = DeviceIdentificationNumber.from_int(
                        (int(chip_probe_data["cp_device_id"], 16) >> 32) &
                        0xFFFFFFFFFFFFFFFF)
            logging.info(
                f"Updating device ID to: {chip_probe_data['cp_device_id']}")
            self.device_id.update_din(din_from_device)
            self.device_id.pretty_print()

            self._make_log_dir()
            shutil.move(stdout_logfile, f"{self.log_dir}/cp_out.log.txt")
            shutil.move(stderr_logfile, f"{self.log_dir}/cp_err.log.txt")

        self.cp_data = chip_probe_data
        logging.info(f"CP logs saved to {self.log_dir}.")
        logging.info("CP completed successfully.")

    def run_ft(self) -> None:
        """Runs the FT provisioning flow on the target DUT."""
        logging.info("Running FT provisioning ...")

        # Set cmd args and device binaries.
        host_bin = _FT_HOST_BIN.format(sku=self.sku_config.name)
        host_flags = _BASE_PROVISIONING_FLAGS
        individ_elf = _FT_INDIVID_DEVICE_ELF
        # Emulation perso bins are signed online with fake keys, and therefore
        # have different file naming patterns than production SKUs.
        perso_bin = self.sku_config.perso_bin
        fw_bundle_bin = _FT_FW_BUNDLE_BIN
        if self.fpga:
            # Set host flags and device binaries for FPGA DUT.
            # No need to load another bitstream, we will take over where CP
            # stage above left off.
            host_flags = host_flags.format(target=self.fpga,
                                           openocd_bin=_OPENOCD_BIN,
                                           openocd_cfg=_OPENOCD_ADAPTER_CONFIG)
            individ_elf = individ_elf.format(
                base_dir=self._base_dev_dir(),
                otp=self.sku_config.otp,
                target=f"fpga_{self.fpga}_rom_with_fake_keys")
            perso_bin = perso_bin.format(
                base_dir=self._base_dev_dir(),
                sku=self.sku_config.name,
                target=f"fpga_{self.fpga}_rom_with_fake_keys")
            fw_bundle_bin = fw_bundle_bin.format(
                base_dir=self._base_dev_dir(),
                sku=self.sku_config.name,
                target=f"fpga_{self.fpga}_rom_with_fake_keys")
        else:
            # Set host flags and device binaries for Silicon DUT.
            host_flags = host_flags.format(target="teacup",
                                           openocd_bin=_OPENOCD_BIN,
                                           openocd_cfg=_OPENOCD_ADAPTER_CONFIG)
            host_flags += " --disable-dft-on-reset"
            individ_elf = individ_elf.format(base_dir=self._base_dev_dir(),
                                             otp=self.sku_config.otp,
                                             target="silicon_creator")
            perso_bin = perso_bin.format(base_dir=self._base_dev_dir(),
                                         sku=self.sku_config.name,
                                         target="silicon_creator")
            fw_bundle_bin = fw_bundle_bin.format(base_dir=self._base_dev_dir(),
                                                 sku=self.sku_config.name,
                                                 target="silicon_creator")

        # Write CA configs to a JSON tmpfile.
        ca_config_dict = {
            "dice": self.sku_config.dice_ca.to_dict_entry(),
            "ext": self.sku_config.ext_ca.to_dict_entry(),
        }

        with tempfile.NamedTemporaryFile(mode="w+") as ca_config_file:
            json.dump(ca_config_dict, ca_config_file)
            ca_config_file.flush()

            # Assemble FT command.
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
            --target-mission-mode-lc-state="{self.sku_config.target_lc_state}" \
            --rom-ext-measurement="{_ZERO_256BIT_HEXSTR}" \
            --owner-manifest-measurement="{_ZERO_256BIT_HEXSTR}" \
            --owner-measurement="{_ZERO_256BIT_HEXSTR}" \
            --rom-ext-security-version="0" \
            --owner-security-version="0" \
            --ca-config={ca_config_file.name} \
            --token-encrypt-key-der-file={self.sku_config.token_encrypt_key} \
            """

            # Get user confirmation before running command.
            logging.info(f"Running command: {cmd}")
            if self.require_confirmation:
                confirm()

            # Run provisioning flow and collect logs.
            stdout_logfile = f"{self.log_dir}/ft_out.log.txt"
            stderr_logfile = f"{self.log_dir}/ft_err.log.txt"
            res = run(cmd, stdout_logfile, stderr_logfile)
            if res.returncode != 0:
                logging.warning(f"FT failed with exit code: {res.returncode}.")
                confirm()

            self.ft_data = self._extract_json_data("PROVISIONING_DATA",
                                                   stdout_logfile)

            # TODO: check device ID from device matches one constructed on host.
            self.device_id = DeviceId.from_hexstr(self.ft_data["device_id"])

            logging.info("FT completed successfully.")
