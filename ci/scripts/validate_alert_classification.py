#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""
Script to validate alert classification arrays and digests.

This script validates that the number of values in alert classification arrays
matches the number of alerts in the alert handler configuration and also
validates/updates digest values by parsing the HJSON configuration files.
"""

import argparse
from pathlib import Path
import subprocess
import sys
from typing import Any, Dict, Tuple
import hjson
import re


REGS_OUTPUT_FILE = "sw/host/opentitanlib/src/otp/alert_handler_regs.rs"


def find_item_in_cfg(cfg_data: Dict[str, Any], item_name: str) -> Dict[str, Any]:
    """Finds an item by name in the parsed owner_sw_cfg data."""
    # Assumes the structure is partitions -> list -> items -> list
    for partition in cfg_data.get("partitions", []):
        for item in partition.get("items", []):
            if item.get("name") == item_name:
                return item
    raise ValueError(f"Could not find item '{item_name}' in the configuration structure.")


def validate_alert_classification(alert_cfg: Dict[str, Any], owner_cfg: Dict[str, Any]) -> bool:
    print("=== Alert Classification Validation ===")
    print("Extracting alert counts from alert handler...")

    try:
        alert_count = int(alert_cfg["param_values"]["n_alerts"])
        loc_alert_count = int(alert_cfg["param_values"]["n_loc_alert"])
    except (ValueError, KeyError) as e:
        print(f"Error: Could not parse alert counts from alert config data: {e}")
        return False

    try:
        alert_class_item = find_item_in_cfg(owner_cfg, "OWNER_SW_CFG_ROM_ALERT_CLASSIFICATION")
        classification_count = len(alert_class_item["value"])
        local_alert_class_item = find_item_in_cfg(
            owner_cfg, "OWNER_SW_CFG_ROM_LOCAL_ALERT_CLASSIFICATION"
        )
        local_classification_count = len(local_alert_class_item["value"])
    except (KeyError, TypeError) as e:
        print(f"Error: Could not parse classification counts from owner SW config data: {e}")
        return False

    alert_match = alert_count == classification_count
    local_alert_match = loc_alert_count == local_classification_count

    print("\n    Alert Classification Results:")
    print(f"    Alert Handler Alerts: {alert_count}")
    print(f"    Alert Classification Values: {classification_count}")
    print(f"    Alert Handler Local Alerts: {loc_alert_count}")
    print(f"    Local Alert Classification Values: {local_classification_count}")

    if alert_match and local_alert_match:
        print("\nSUCCESS: Alert classification validation passed!")
        return True
    else:
        print("\nALERT CLASSIFICATION VALIDATION FAILED:")
        if not alert_match:
            print(
                f"    Regular alerts: handler has {alert_count}, config has {classification_count}"
            )
        if not local_alert_match:
            print(
                f"    Local alerts: handler has {loc_alert_count}, "
                f"config has {local_classification_count}"
            )
        return False


def validate_digest_values(
    alert_handler_file: Path, owner_sw_cfg_file: Path, owner_cfg: Dict[str, Any]
) -> Tuple[bool, Dict[str, str]]:
    """Validates digest values using pre-parsed HJSON data.

    This function compares the current digest values in the owner SW configuration
    against the expected digest values calculated using opentitantool. It validates
    four specific digest values: PROD, PROD_END, DEV, and RMA.

    Args:
        alert_handler_file: Path to the alert_handler_ipconfig.hjson file used
                            to generate alert handler registers for digest calculation
        owner_sw_cfg_file: Path to the owner_sw_cfg.hjson file used as input
                           to opentitantool for digest calculation
        owner_cfg: Pre-parsed HJSON data from the owner SW configuration file
                   containing the current digest values to validate

    Returns:
        Tuple[bool, Dict[str, str]]: A tuple containing:
            - bool: True if all digest values match expected values, False otherwise
            - Dict[str, str]: Dictionary of expected digest values in hex format.
                              Empty dict if validation passes, populated dict if
                              validation fails (used for updating digest values)
    """
    print("\n=== Digest Validation ===")
    print("Validating digest values...")

    alert_lc_states = ["DEV", "PROD", "PROD_END", "RMA"]
    prefix = "OWNER_SW_CFG_ROM_ALERT_DIGEST_"

    def digest_name(lc_state: str) -> str:
        return f"{prefix}{lc_state}"

    digest_names = [digest_name(lc_state) for lc_state in alert_lc_states]

    try:
        print("    Current digest values:")
        current_digests = {}
        for name in digest_names:
            value = find_item_in_cfg(owner_cfg, name)["value"]
            current_digests[name] = value
            print(f"    {name}: {value}")
    except (KeyError, TypeError) as e:
        print(f"Error: Could not parse digest values from owner SW config data: {e}")
        return False, {}

    print("    Generating expected digest values using opentitantool...")
    alert_handler_regtool_file = alert_handler_file.parent / "alert_handler.hjson"

    try:
        print("    Generating alert handler registers...")
        subprocess.run(
            ["./util/regtool.py", alert_handler_regtool_file, "-R", "-o", REGS_OUTPUT_FILE],
            check=True,
            capture_output=True,
            text=True,
        )

        print("    Running opentitantool to calculate expected digest values...")
        cmd = [
            "./bazelisk.sh",
            "run",
            "//sw/host/opentitantool",
            "--",
            "--rcfile=''",
            "otp",
            "alert-digest",
            owner_sw_cfg_file.as_posix(),
        ]
        print(f"    Command: {' '.join(cmd)}")
        result = subprocess.run(cmd, check=True, capture_output=True, text=True)
        opentitantool_output = result.stdout

    except subprocess.CalledProcessError as e:
        print(f"Error: Failed to generate expected digest values: {e}")
        return False, {}
    finally:
        subprocess.run(["git", "checkout", "--", REGS_OUTPUT_FILE], capture_output=True)

    expected_digests_hex = {}
    try:
        expected_cfg = hjson.loads(opentitantool_output)
        # Navigate the standard partitions -> items structure from the tool output
        digest_list = expected_cfg["partitions"][0]["items"]
        for item in digest_list:
            item_name = item.get("name")
            item_value = item.get("value")
            if item_name and item_value is not None:
                expected_digests_hex[item_name] = hex(int(item_value))
    except (ValueError, KeyError, TypeError, IndexError) as e:
        print(f"Error: Could not parse digest values from opentitantool output: {e}")
        print("Full output was:\n", opentitantool_output)
        return False, {}

    print("    Expected digest values:")
    for name, value in expected_digests_hex.items():
        lc_state = name.split(prefix)[-1]
        print(f"      {lc_state}: {value} ({int(value, 16)})")

    digest_match = all(
        current_digests[name].lower() == expected_digests_hex[name].lower() for name in digest_names
    )

    print("\n    Digest Validation Results:")
    print(f"    Digest Values Match: {'YES' if digest_match else 'NO'}")

    if digest_match:
        print("\nSUCCESS: Digest validation passed!")
        print("    Digest values: All match expected values")
        return True, {}
    else:
        print("\nDIGEST VALIDATION FAILED:")
        print("    Digest values: Current values do not match expected values")
        print("    Use --update flag to automatically update digest values")
        return False, expected_digests_hex


def perform_update(owner_sw_cfg_file: str, expected_digests: Dict[str, str]):
    """Performs a precise, line-by-line text replacement to update only the
    digest item values, preserving all comments and formatting.
    """
    print("\nUpdate mode enabled...")
    print("    Updating digest values...")
    try:
        with open(owner_sw_cfg_file, "r") as f:
            lines = f.readlines()

        new_lines = []
        active_digest_to_update = None

        for line in lines:
            is_new_item_line = 'name:' in line and re.search(r'^\s*name:', line)

            if is_new_item_line:
                # If we were looking for a value but found a new item, stop looking.
                active_digest_to_update = None
                # Check if this new item is a digest we need to update.
                for name in expected_digests.keys():
                    if f'"{name}"' in line or f" {name}" in line:
                        active_digest_to_update = name
                        break

            # If we are inside a digest block, look for its value line to replace.
            elif active_digest_to_update and 'value:' in line and re.search(r'^\s*value:', line):
                new_value = expected_digests[active_digest_to_update]
                # Replace the old value using regex, preserving surrounding text.
                line = re.sub(r'(value:\s*)"0x[0-9a-fA-F]*"',
                              fr'\1"{new_value}"', line)
                # Reset state after the update is done for this item.
                active_digest_to_update = None

            new_lines.append(line)

        with open(owner_sw_cfg_file, "w") as f:
            f.writelines(new_lines)

    except (IOError, ValueError) as e:
        print(f"Error updating file {owner_sw_cfg_file}: {e}")
        sys.exit(1)

    print("    SUCCESS: Digest values updated successfully!")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--update",
        action="store_true",
        help="Update the digest values in the owner_sw_cfg.hjson file.",
    )
    parser.add_argument("alert_handler_file",
                        type=Path,
                        help="Path to alert_handler_ipconfig.hjson file.")
    parser.add_argument("owner_sw_cfg_file",
                        type=Path,
                        help="Path to owner_sw_cfg.hjson file.")
    args = parser.parse_args()

    try:
        for f in [args.alert_handler_file, args.owner_sw_cfg_file]:
            if not f.is_file():
                raise FileNotFoundError(f"File not found '{f}'")

        with open(args.alert_handler_file, "r") as f:
            alert_cfg_data = hjson.load(f)
        with open(args.owner_sw_cfg_file, "r") as f:
            owner_cfg_data = hjson.load(f, use_decimal=True)
    except (FileNotFoundError, IOError, ValueError) as e:
        print(f"Error: {e}")
        sys.exit(1)

    if not validate_alert_classification(alert_cfg_data, owner_cfg_data):
        print("\nERROR: Alert classification validation failed!")
        sys.exit(1)

    digest_match, expected_digests = validate_digest_values(
        args.alert_handler_file, args.owner_sw_cfg_file, owner_cfg_data
    )

    if digest_match:
        print("\nSUCCESS: All validations passed!")
        sys.exit(0)

    if args.update:
        perform_update(args.owner_sw_cfg_file, expected_digests)
        print("\nPerforming post-update digest validation...")

        # Re-read the file to get the updated values for validation.
        with open(args.owner_sw_cfg_file, "r") as f:
            updated_owner_cfg_data = hjson.load(f)

        post_update_match, _ = validate_digest_values(
            args.alert_handler_file, args.owner_sw_cfg_file, updated_owner_cfg_data
        )
        if post_update_match:
            print("\nSUCCESS: All validations passed after update!")
        else:
            print("\nERROR: Digest validation still failed after update!")
            sys.exit(1)
    else:
        print("\nERROR: Digest validation failed!")
        sys.exit(1)


if __name__ == "__main__":
    main()
