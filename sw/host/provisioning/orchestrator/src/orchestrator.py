# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Earlgrey benchtop provisioning orchestrator."""

import argparse
import logging
import shlex
import subprocess
import sys
from pathlib import Path

import hjson

import db
from device_id import DeviceId, DeviceIdentificationNumber
from ot_dut import OtDut
from sku_config import SkuConfig
from util import confirm, parse_hexstring_to_int, resolve_runfile


def get_user_confirmation(
    sku_config: SkuConfig,
    device_id: DeviceId,
    commit_hash: str,
    args: argparse.Namespace,
) -> None:
    """Gets user confirmation after printing provisioning inputs to console."""
    print(
        "\nPlease confirm the following values (> indicates generated values):"
    )
    print("[DEVICE ID]")
    device_id.pretty_print()
    print(f"""
[SKU CONFIG]
SKU:      {sku_config.name}
LC State: {sku_config.target_lc_state}

[OTHER]
fpga:          {args.fpga}
> commit hash: {commit_hash}

[DICE CA]
certificate: {sku_config.dice_ca.certificate}
key:         {sku_config.dice_ca.key}
key type:    {sku_config.dice_ca.key_type}
key ID:      {sku_config.dice_ca.key_id}
""")
    if sku_config.ext_ca:
        print(f"""

[EXTENSION CA]
certificate: {sku_config.ext_ca.certificate}
key:         {sku_config.ext_ca.key}
key type:    {sku_config.ext_ca.key_type}
key ID:      {sku_config.ext_ca.key_id}
""")
    if not args.non_interactive:
        confirm()


def main(args_in):
    # Setup logging.
    logging.basicConfig(
        level=logging.DEBUG,
        handlers=[
            logging.FileHandler("orchestrator.log.txt"),
            logging.StreamHandler(sys.stdout)
        ],
    )

    # Parse cmd line args.
    parser = argparse.ArgumentParser(
        prog=__doc__,
        description=
        """This tool runs the CP and FT provisioning flows on a benchtop
        provisioning setup, and records the results into a local and/or remote
        provisioning database.""",
    )
    parser.add_argument(
        "--sku-config",
        required=True,
        type=str,
        help="SKU HJSON configuration file.",
    )
    parser.add_argument(
        "--ast-cfg-version",
        required=True,
        type=int,
        help="AST configuration version to be written to OTP.",
    )
    parser.add_argument(
        "--package",
        type=str,
        help="Override of package string that is in the SKU config.",
    )
    parser.add_argument(
        "--test-unlock-token",
        required=True,
        type=parse_hexstring_to_int,
        help="Raw test unlock token to inject into OTP SECRET0 partition.",
    )
    parser.add_argument(
        "--test-exit-token",
        required=True,
        type=parse_hexstring_to_int,
        help="Raw test exit token to inject into OTP SECRET0 partition.",
    )
    parser.add_argument(
        "--fpga",
        choices=["cw310", "cw340"],
        help="Run flow on FPGA (instead of silicon).",
    )
    parser.add_argument(
        "--fpga-dont-clear-bitstream",
        action="store_true",
        help="If set, the FPGA bitsream will not be cleared before CP.",
    )
    parser.add_argument(
        "--log-ujson-payloads",
        action="store_true",
        default=False,
        help="Log UJSON host-->device payloads to console for ATE development.",
    )
    parser.add_argument(
        "--non-interactive",
        action="store_true",
        default=False,
        help="Skip all non-required user confirmations.",
    )
    parser.add_argument(
        "--log-dir",
        default="logs",
        help="Root directory to store log files under.",
    )
    parser.add_argument(
        "--cp-only",
        action="store_true",
        help="If set, only run CP stage (skips FT and database write).",
    )
    parser.add_argument(
        "--db-path",
        required=False,
        help=
        "Path to provisioning database. The database will be created if it does not exist.",
    )
    args = parser.parse_args(args_in)

    if not args.cp_only and args.db_path is None:
        parser.error("--db-path is required when --cp-only is not provided")

    # Load and validate a SKU configuration file.
    sku_config_path = resolve_runfile(args.sku_config)
    sku_config_args = {}
    with open(sku_config_path, "r") as fp:
        sku_config_args = hjson.load(fp)
    sku_config = SkuConfig(ast_cfg_version=args.ast_cfg_version,
                           **sku_config_args)

    # Override package ID if requested.
    if args.package:
        sku_config.package = args.package
        sku_config.validate()
        sku_config.load_hw_ids()

    # The device identification number is determined during CP by extracting data
    # from the device.
    din = DeviceIdentificationNumber.blind_asm()
    device_id = DeviceId(sku_config, din)

    # TODO: Setup remote and/or local DB connections.
    # TODO: Check if the device ID is present in the DB.

    # Generate commit hash of current provisioning run.
    commit_hash = subprocess.run(shlex.split("git rev-parse HEAD"),
                                 capture_output=True,
                                 text=True).stdout.strip()

    # Run all provisioning flows.
    get_user_confirmation(sku_config, device_id, commit_hash, args)
    dut = OtDut(logs_root_dir=args.log_dir,
                sku_config=sku_config,
                device_id=device_id,
                test_unlock_token=args.test_unlock_token,
                test_exit_token=args.test_exit_token,
                fpga=args.fpga,
                fpga_dont_clear_bitstream=args.fpga_dont_clear_bitstream,
                log_ujson_payloads=args.log_ujson_payloads,
                require_confirmation=not args.non_interactive)
    dut.run_cp()
    if args.cp_only:
        logging.info("FT skipped since --cp-only was provided")
        return
    dut.run_ft()

    # Open the local SQLite registry database.
    db_path = Path(args.db_path)
    db_handle = db.DB(db.DBConfig(db_path=db_path))
    db.DeviceRecord.create_table(db_handle)

    # Check device ID exists in the database.
    if db.DeviceRecord.query(db_handle, dut.device_id.to_hexstr()) is not None:
        logging.warning(
            "DeviceId already exists in database. Overwrite record?")
        confirm()

    # Register the DUT in the database.
    device_record = db.DeviceRecord.from_dut(dut)
    device_record.upsert(db_handle)
    logging.info(f"Added DeviceRecord to database: {device_record}")


if __name__ == "__main__":
    main(sys.argv[1:])
