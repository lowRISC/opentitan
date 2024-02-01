# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import binascii
import datetime
import logging
import os
import shlex
import sqlite3
import struct
import subprocess
import sys

from google.auth.exceptions import DefaultCredentialsError

from ot_device import OTDevice
from update_remote_db import update_remote_db
from util import (format_hex, confirm, bytes_to_int, parse_hexstring_to_int,
                  parse_str_to_ascii_bytes, OT_SQL_TABLE_NAME)


def setup_db(db_filename, log_archive_root):
    """Set up the provisioning database.

    This function should be idempotent.

    Returns:
    db_conn - a database connecion
    """
    db_conn = sqlite3.connect(db_filename)
    cur = db_conn.cursor()
    cur.execute(f"""
                CREATE TABLE IF NOT EXISTS {OT_SQL_TABLE_NAME} (
                    device_id STRING NOT NULL PRIMARY KEY,
                    test_unlock_token STRING,
                    test_exit_token STRING,
                    enc_rma_unlock STRING,
                    device_ecc_pub_key_x STRING,
                    device_ecc_pub_key_y STRING,
                    host_ecc_priv_keyfile STRING,
                    uds_cert_pub_key_x STRING,
                    uds_cert_pub_key_y STRING,
                    lc_state STRING,
                    sku STRING,
                    commit_hash STRING,
                    timestamp STRING)
    """)

    # Create the directory that holds the logs.
    os.makedirs(log_archive_root, exist_ok=True)

    return db_conn


def make_device_id(si_creator_id, product_id, chip_revision, package_id,
                   serial_num):
    """Create the full 256-bit device ID

    Each parameter should be written as a little-endian formatted hex string

    Arguments:
    si_creator_id (2 bytes): Silicon Creator identifier. Assigned by the OpenTitan project
    product_id (2 bytes): Product identifier. Assigned by the Silicon Creator
    chip_revision (2 bytes): [Device UID] ASCII chip revision identifier
    package_id (2 bytes): [Device UID] ASCII package identifier
    serial_num (2 bytes): [Device UID] uint16_t serial number
    """

    device_uid = struct.pack("<HHHH", serial_num, bytes_to_int(package_id), 0,
                             bytes_to_int(chip_revision))
    logging.debug(f"[Device ID] device_uid: {device_uid}")
    logging.debug(
        f"[Device ID] device_uid: {format_hex(bytes_to_int(device_uid), width=16)}"
    )

    # HW origin contains:
    # - 16 bits SiCreator ID
    # - 16 bits Product ID
    # - 64 bits Device UID
    hw_origin = struct.pack("<HH8s", si_creator_id, product_id, device_uid)
    logging.debug(
        f"[Device ID] hw_origin: {format_hex(bytes_to_int(hw_origin), width=24)}"
    )

    crc = binascii.crc32(hw_origin)
    full_hw_origin = struct.pack("<12sI", hw_origin, crc)
    logging.debug(
        f"[Device ID] full_hw_origin: {format_hex(bytes_to_int(full_hw_origin), width=32)}"
    )

    # Repeat the hw origin information in the sku_specific_info section
    sku_specific_info = full_hw_origin

    # Assemble full device ID
    device_id_bytes = struct.pack("<16s16s", full_hw_origin, sku_specific_info)
    device_id = bytes_to_int(device_id_bytes)
    logging.debug(f"[Device ID] device_id: {format_hex(device_id, width=64)}")

    return device_id


def main():
    logging.basicConfig(
        level=logging.DEBUG,
        handlers=[
            logging.FileHandler("orchestrator.log.txt"),
            logging.StreamHandler(sys.stdout)
        ],
    )

    parser = argparse.ArgumentParser(
        prog="OT ES Provisioning Orchestrator",
        description=
        "This tool runs the CP and FT programs and records the results.",
    )
    parser.add_argument("--si_creator_id",
                        required=True,
                        type=parse_hexstring_to_int)
    parser.add_argument("--product_id",
                        required=True,
                        type=parse_hexstring_to_int)
    parser.add_argument("--serial_num",
                        required=True,
                        type=parse_hexstring_to_int)
    parser.add_argument("--package_id",
                        required=True,
                        type=parse_str_to_ascii_bytes)
    parser.add_argument("--chip_revision",
                        required=True,
                        type=parse_str_to_ascii_bytes)
    parser.add_argument("--test_unlock_token",
                        required=True,
                        type=parse_hexstring_to_int)
    parser.add_argument("--test_exit_token",
                        required=True,
                        type=parse_hexstring_to_int)
    parser.add_argument("--ecc_priv_keyfile", required=True)
    parser.add_argument("--target_lc_state",
                        help="Target mission mode LC state",
                        choices=["dev", "prod"],
                        required=True)
    parser.add_argument("--sku",
                        help="SKU",
                        choices=["prodc", "sival", "sival_bringup"],
                        required=True)
    parser.add_argument("--fpga_test",
                        action="store_true",
                        help="Run on FPGA targets",
                        default=False)
    parser.add_argument("--non_interactive",
                        action="store_true",
                        help="Skip all non-required confirmations",
                        default=False)
    parser.add_argument("--db_file",
                        default="earlgrey_z1.db",
                        help="Database file")
    parser.add_argument("--log_archive_root",
                        default="logs",
                        help="Root directory to store log files under.")
    parser.add_argument("--cloud_project",
                        default=None,
                        help="Name of Google Cloud project with Firestore database to update. "
                             "If not provided, entries will be cached locally.")
    args = parser.parse_args()

    db_conn = setup_db(args.db_file, args.log_archive_root)

    device_id = make_device_id(args.si_creator_id, args.product_id,
                               args.chip_revision, args.package_id,
                               args.serial_num)

    # Check if the device ID is present in the DB
    logging.debug("Checking for duplicate Device ID in DB...")
    device_id_str = format_hex(device_id, width=64)
    res = db_conn.cursor().execute(
        f"SELECT device_id FROM {OT_SQL_TABLE_NAME} WHERE device_id='{device_id_str}'"
    )
    existing_devices = res.fetchall()
    if len(existing_devices) > 0:
        logging.warning(
            f"Device ID {device_id_str} already exists in the database." +
            " Database write will fail if you contine."
        )
        confirm()
    else:
        logging.debug("Did not find duplicate Device ID in DB. Continuing")

    # Generate some metadata
    commit_hash = subprocess.run(shlex.split("git rev-parse HEAD"),
                                 capture_output=True,
                                 text=True).stdout.strip()
    ecc_keyfile_basename = os.path.basename(args.ecc_priv_keyfile)

    print(
        "\nPlease confirm the following values (> indicates generated values):"
    )
    print(f"""
          [DEVICE ID]
          si_creator_id: {format_hex(args.si_creator_id, width = 4)}
          product_id: {format_hex(args.product_id, width = 4)}
          serial_num: {format_hex(args.serial_num, width = 2)}
          chip_revision: {args.chip_revision}
          package_id: {args.package_id}
          > device_id: {format_hex(device_id, width=64)}

          [TOKENS]
          test_unlock_token: {format_hex(args.test_unlock_token, width=32)}
          test_exit_token: {format_hex(args.test_exit_token, width=32)}

          [ECC PRIVATE KEYFILE]
          keyfile path: {args.ecc_priv_keyfile}
          > keyfile basename (stored in DB): {ecc_keyfile_basename}

          [OTHER]
          target_lc_state: {args.target_lc_state}
          sku: {args.sku}
          > commit hash: {commit_hash}
          """)

    if not args.non_interactive:
        confirm()

    timestamp = datetime.datetime.now(datetime.timezone.utc).isoformat()

    chip = OTDevice(device_id, args.test_unlock_token, args.test_exit_token,
                    args.target_lc_state, args.sku, args.fpga_test,
                    args.log_archive_root)
    chip.cp_provision(require_confirmation=not args.non_interactive)
    chip.ft_provision(args.ecc_priv_keyfile,
                      require_confirmation=not args.non_interactive)
    chip.parse_logs()
    chip.record_device(db_conn, commit_hash, timestamp, ecc_keyfile_basename)

    if args.cloud_project:
        try:
            update_remote_db(args.cloud_project, db_conn)
        except DefaultCredentialsError:
            logging.warning(
                "Updating remote provisioning database failed: not authenticated to gcloud"
            )
        except Exception as e:
            logging.warning(
                f"Updating remote provisioning database failed: {e}"
            )
    else:
        logging.warning("--cloud_project was not provided. Skipping remote database upload")

    logging.info("Provisioning complete")

    res = db_conn.cursor().execute(f"SELECT * FROM {OT_SQL_TABLE_NAME}")
    rows = res.fetchall()
    if len(rows) == 0:
        logging.info(f"All local records uploaded! You may safely delete {args.db_file}")
    else:
        logging.warning(f"{len(rows)} record(s) remaining in {args.db_file}")
        logging.warning("Run update_remote_db.py to upload remaining records")


if __name__ == "__main__":
    main()
