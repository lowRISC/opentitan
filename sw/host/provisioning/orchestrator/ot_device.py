# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
import json
import logging
import os
import re
import sqlite3

from util import OT_SQL_TABLE_NAME, confirm, format_hex, run


class OTDevice:

    def __init__(self, device_id, test_unlock_token, test_exit_token,
                 target_lc_state, sku, fpga_test, log_archive_root):
        """Class representing an Opentitan Device being provisioned.

        Arguments:
        device_id -- Device ID defined by the Silicon Creator and specified in
            https://opentitan.org/book/doc/security/specs/identities_and_root_keys/#device-identifier
        test_unlock_token -- Test-Unlock token
        test_exit_token -- Test-exit token
        target_lc_state -- final lifecycle state of the device after provisioning.
            Must be dev or prod.
        sku -- OTP image to use. Must be sival or sival_bringup.
        fpga_test -- Boolean indicating if the FPGA test flow should be executed.
        log_archive_root -- Root directory to store log files under.
        """
        self.test_unlock_token = test_unlock_token
        self.test_exit_token = test_exit_token
        self.target_lc_state = target_lc_state
        self.device_id = device_id
        self.sku = sku
        self.fpga_test = fpga_test

        # Strip the 0x from the front of the directory name
        self.log_dir = f"{log_archive_root}/{format_hex(self.device_id, width=64)[2:]}"
        if os.path.exists(self.log_dir):
            logging.warning(
                f"Log file {self.log_dir} already exists. Continue to overwrite"
            )
            confirm()

        os.makedirs(self.log_dir, exist_ok=True)

    def cp_provision(self, require_confirmation=True):
        """Run the CP provisioning Bazel target."""
        logging.info("Running CP Provisioning")

        elf_path = "sw/device/silicon_creator/manuf/skus/earlgrey_a0/sival_bringup/{}"
        if self.fpga_test:
            platform_harness_flags = """--interface=cw310 \
--clear-bitstream --bitstream=hw/bitstream/rom_with_fake_keys_otp_raw.bit \
--openocd=third_party/openocd/build_openocd/bin/openocd \
--openocd-adapter-config=external/openocd/tcl/interface/ftdi/olimex-arm-usb-tiny-h.cfg"""
            elf = elf_path.format(
                "sram_cp_provision_fpga_cw310_rom_with_fake_keys.elf")
        else:
            platform_harness_flags = """--interface=teacup \
--disable-dft-on-reset \
--openocd=third_party/openocd/build_openocd/bin/openocd \
--openocd-adapter-config=external/openocd/tcl/interface/cmsis-dap.cfg"""
            elf = elf_path.format("sram_cp_provision_silicon_creator.elf")

        # Assemble bazel command
        cmd = f"""bazel run //sw/host/provisioning/cp -- \
--rcfile= --logging=info \
{platform_harness_flags} \
--elf={elf} \
--device-id="{format_hex(self.device_id, width=64)}" \
--test-unlock-token="{format_hex(self.test_unlock_token, width=32)}" \
--test-exit-token="{format_hex(self.test_exit_token, width=32)}" \
--manuf-state=0x00000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000 \
--wafer-auth-secret=0x00000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000"""

        logging.info(f"Running command: {cmd}")
        if require_confirmation:
            confirm()

        res = run(cmd, f"{self.log_dir}/cp_out.log.txt",
                  f"{self.log_dir}/cp_err.log.txt")

        if res.returncode != 0:
            logging.warning(
                f"cp_provisioning returned with non-zero exit code: {res.returncode}." +
                " Logs have been written but no database entry has been made yet."
            )
            confirm()
        else:
            logging.info("CP completed successfully")

    def ft_provision(self,
                     ecc_priv_keyfile,
                     ca_priv_keyfile,
                     ca_certfile,
                     ca_key_id,
                     mission_mode_state,
                     require_confirmation=True):
        """Run the FT provisioning Bazel target."""
        logging.info("Running FT Provisioning")

        sram_ft_indiv_elf_path = "sw/device/silicon_creator/manuf/skus/earlgrey_a0/sival_bringup/sram_ft_individualize_{}_{}.elf"  # noqa: E501
        # Default to prod signed binaries unless in DEV state.
        perso_bin_path = "sw/device/silicon_creator/manuf/skus/earlgrey_a0/sival_bringup/"  # noqa: E501
        if mission_mode_state == "dev":
            perso_bin_path += "{}"
        else:
            perso_bin_path += "binaries/{}"

        if self.fpga_test:
            elf = sram_ft_indiv_elf_path.format(
                self.sku, "fpga_cw310_rom_with_fake_keys")
            signing_key = "{}_key_0".format(mission_mode_state)
            bazel_suffix = "fpga_cw310_rom_with_fake_keys.{}.signed.bin".format(signing_key)

            bootstrap = perso_bin_path.format(
                "ft_personalize_1_{}".format(bazel_suffix)
            )
            bootstrap2 = perso_bin_path.format(
                "ft_personalize_2_{}".format(bazel_suffix)
            )
            bootstrap3 = perso_bin_path.format(
                "ft_personalize_3_{}".format(bazel_suffix)
            )
            bootstrap4 = perso_bin_path.format(
                "ft_personalize_4_{}".format(bazel_suffix)
            )

            platform_bazel_flags = ""
            platform_harness_flags = """--interface=cw310 --clear-bitstream \
--bitstream=sw/host/provisioning/ft/ft_test_bitstream.bit \
--openocd=third_party/openocd/build_openocd/bin/openocd \
--openocd-adapter-config=external/openocd/tcl/interface/ftdi/olimex-arm-usb-tiny-h.cfg"""

        else:
            elf = sram_ft_indiv_elf_path.format(self.sku, "silicon_creator")
            signing_key = "earlgrey_a0_{}_0".format(mission_mode_state)
            bazel_suffix = "silicon_creator.{}.signed.bin".format(signing_key)

            bootstrap = perso_bin_path.format(
                "ft_personalize_1_{}".format(bazel_suffix)
            )
            bootstrap2 = perso_bin_path.format(
                "ft_personalize_2_{}".format(bazel_suffix)
            )
            bootstrap3 = perso_bin_path.format(
                "ft_personalize_3_{}".format(bazel_suffix)
            )
            bootstrap4 = perso_bin_path.format(
                "ft_personalize_4_{}".format(bazel_suffix)
            )

            platform_bazel_flags = "--//signing:token=//signing/tokens:nitrokey"
            platform_harness_flags = """--interface=teacup \
--disable-dft-on-reset \
--openocd=third_party/openocd/build_openocd/bin/openocd \
--openocd-adapter-config=external/openocd/tcl/interface/cmsis-dap.cfg"""

        cmd = f"""bazel run //sw/host/provisioning/ft {platform_bazel_flags} -- \
--rcfile= --logging=info \
{platform_harness_flags} \
--elf={elf} \
--bootstrap={bootstrap} \
--second-bootstrap={bootstrap2} \
--third-bootstrap={bootstrap3}  \
--fourth-bootstrap={bootstrap4}  \
--device-id="{format_hex(self.device_id, 64)}" \
--test-unlock-token="{format_hex(self.test_unlock_token, width=32)}" \
--test-exit-token="{format_hex(self.test_exit_token, width=32)}" \
--target-mission-mode-lc-state="{self.target_lc_state}" \
--host-ecc-sk={ecc_priv_keyfile} \
--cert-endorsement-ecc-sk={ca_priv_keyfile} \
--ca-certificate={ca_certfile} \
--rom-ext-measurement=0x00000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000  \
--owner-manifest-measurement=0x00000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000  \
--owner-measurement=0x00000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000  \
--uds-auth-key-id={ca_key_id} \
--rom-ext-security-version="0" \
--owner-security-version="0" \
"""  # noqa: E501

        logging.info(f"Running command: {cmd}")
        if require_confirmation:
            confirm()
        res = run(cmd, f"{self.log_dir}/ft_out.log.txt",
                  f"{self.log_dir}/ft_err.log.txt")

        if res.returncode != 0:
            logging.warning(
                f"ft_provisioning returned with non-zero return code: {res.returncode}." +
                " Logs have been written but no database entry has been made yet."
            )
            confirm()
        else:
            logging.info("FT completed successfully")

    def parse_logs(self):
        logging.info("Extracting values from logs...")
        # Extract output from logs
        with open(f"{self.log_dir}/ft_out.log.txt", "rb") as f:
            stdout = f.read().decode(encoding="ascii",
                                     errors="backslashreplace")

        rma_msg_matches = re.findall(
            r"(\{\"wrapped_rma_unlock_token\":.*) CRC:.*", stdout)
        if len(rma_msg_matches) != 1:
            logging.error(
                f"Expected 1 RMA unlock token message, found these messages: {rma_msg_matches}"
            )

        # TODO: UDS certs cannot currently be provisioned in ft_personalize_3. Write a zero for now.
        # uds_cert_msg_matches = re.findall("RESP_OK:(\{\"uds_certificate\":.*) CRC:.*", stdout)
        # if len(uds_cert_msg_matches) != 1:
        #     logging.error(f"Expected 1 UDS certificate message, found these messages: {uds_cert_msg_matches}")  # noqa: E501

        logging.debug("Found RESP_OK messages")

        # First match is the RMA unlock token payload
        wrapped_key = ""
        device_pk = {"x": "", "y": ""}
        if rma_msg_matches:
            rma_payload = json.loads(rma_msg_matches[0])
            wrapped_key = rma_payload["wrapped_rma_unlock_token"]["data"]
            device_pk = rma_payload["wrapped_rma_unlock_token"]["device_pk"]
        # TODO: parse these keys
        self.enc_rma_unlock = str(wrapped_key)
        self.device_ecc_pub_key_x = str(device_pk["x"])
        self.device_ecc_pub_key_y = str(device_pk["y"])

        # Second match is the certificate payload.
        # TODO: parse the certificate payload
        self.uds_cert_pub_key_x = "0"
        self.uds_cert_pub_key_y = "0"

    def record_device(self, db_conn, commit_hash, timestamp,
                      ecc_keyfile_basename):
        logging.info("Writing outputs to DB")
        table_values = [
            format_hex(self.device_id, width=64),
            format_hex(self.test_unlock_token, width=32),
            format_hex(self.test_exit_token, width=32),
            self.enc_rma_unlock,
            self.device_ecc_pub_key_x,
            self.device_ecc_pub_key_y,
            ecc_keyfile_basename,
            self.uds_cert_pub_key_x,
            self.uds_cert_pub_key_y,
            self.target_lc_state,
            self.sku,
            commit_hash,
            timestamp,
        ]
        sql_cmd = f"INSERT INTO {OT_SQL_TABLE_NAME} VALUES ("
        for i in table_values:
            sql_cmd += f"\"{i}\","
        # Remove last comma
        sql_cmd = sql_cmd[:-1]
        sql_cmd += ")"

        logging.debug(f"Executing SQL command: {sql_cmd}")
        try:
            db_conn.cursor().execute(sql_cmd)
            db_conn.commit(
            )  # INSERT statement implicitly opens a SQL transaction that must be committed
        except sqlite3.IntegrityError:
            logging.warning(f"SQL command failed executing: {sql_cmd}")

        # Write out metadata to filesystem backup
        with open(f"{self.log_dir}/metadata.log.txt", "w") as f:
            f.write(commit_hash)
            f.write(timestamp)
