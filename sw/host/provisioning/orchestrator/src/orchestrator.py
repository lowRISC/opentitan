# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Earlgrey benchtop provisioning orchestrator."""

import argparse
import logging
import shlex
import subprocess
import sys

import hjson

from device_id import DeviceId, DeviceIdentificationNumber
from ot_dut import OtDut
from sku_config import SkuConfig
from util import confirm, parse_hexstring_to_int


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

[DICE CA]
certificate: {sku_config.dice_ca.certificate}
key:         {sku_config.dice_ca.key}
key type:    {sku_config.dice_ca.key_type}
key ID:      {sku_config.dice_ca.key_id}

[EXTENSION CA]
certificate: {sku_config.ext_ca.certificate}
key:         {sku_config.ext_ca.key}
key type:    {sku_config.ext_ca.key_type}
key ID:      {sku_config.ext_ca.key_id}

[OTHER]
fpga:          {args.fpga}
> commit hash: {commit_hash}
""")
    if not args.non_interactive:
        confirm()


def main():
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
        "--rma-unlock-token",
        required=True,
        type=parse_hexstring_to_int,
        help="Raw RMA token to inject into OTP SECRET2 partition.",
    )
    parser.add_argument(
        "--fpga",
        choices=["hyper310", "cw340"],
        help="Run flow on FPGA (instead of silicon).",
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
    args = parser.parse_args()

    # Load and validate a SKU configuration file.
    sku_config_args = {}
    with open(args.sku_config, "r") as fp:
        sku_config_args = hjson.load(fp)
    sku_config = SkuConfig(**sku_config_args)

    # Create a (unique) device identification number and device ID.
    # TODO: update this by extracting data from the device during CP.
    din = DeviceIdentificationNumber(
        year=0,
        week=0,
        lot=0,
        wafer=0,
        wafer_x_coord=0,
        wafer_y_coord=0,
    )
    device_id = DeviceId(sku_config, din)

    # TODO: Setup remote and/or local DV connections.
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
                rma_unlock_token=args.rma_unlock_token,
                fpga=args.fpga,
                require_confirmation=not args.non_interactive)
    dut.run_cp()
    dut.run_ft()
    # TODO: Extract provisioning data from logs and commit to DB.


if __name__ == "__main__":
    main()
