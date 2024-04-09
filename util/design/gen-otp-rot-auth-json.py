#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""Generate ROT creator authentication data from JSON file.

This script generates ROT creator authentication data from a JSON file. The
JSON file should contain the ROT creator authentication data in the following
format:

{
    "partitions": [
        {
            "name": "ROT_CREATOR_AUTH_CODESIGN",
            "items": [
                {
                    "name": "ROT_CREATOR_AUTH_CODESIGN_SPX_KEY_TYPE0",
                    "value": "0x00000001"
                },
                {
                    "name": "ROT_CREATOR_AUTH_CODESIGN_SPX_KEY0",
                    "value": "0x ..."
                },
                {
                    "name": "ROT_CREATOR_AUTH_CODESIGN_SPX_KEY_CONFIG0",
                    "value": "0x00000001"
                },
                {
                    "name": "ROT_CREATOR_AUTH_CODESIGN_ECDSA_KEY_TYPE0",
                    "value": "0x00000001"
                },
                {
                    "name": "ROT_CREATOR_AUTH_CODESIGN_ECDSA_KEY0",
                    "value": "0x ..."
                }
                ...
            ]
        }
    ]
}

The script will generate the ROT creator authentication data and update the JSON
file with the generated ROT_CREATOR_AUTH_CODESIGN_BLOCK_SHA2_256_HASH.
"""

import argparse
import binascii
import json

import hjson
from Crypto.Hash import SHA256

_PARTITION_NAME = "ROT_CREATOR_AUTH_CODESIGN"

_STRUCT_ITEM_NAMES_SPX = [
    "ROT_CREATOR_AUTH_CODESIGN_SPX_KEY_TYPE",
    "ROT_CREATOR_AUTH_CODESIGN_SPX_KEY",
    "ROT_CREATOR_AUTH_CODESIGN_SPX_KEY_CONFIG",
]

_STRUCT_ITEM_NAMES_ECDSA = [
    "ROT_CREATOR_AUTH_CODESIGN_ECDSA_KEY_TYPE",
    "ROT_CREATOR_AUTH_CODESIGN_ECDSA_KEY",
]

_EXPECTED_ITEM_SIZES = {
    "ROT_CREATOR_AUTH_CODESIGN_SPX_KEY_TYPE": 4,
    "ROT_CREATOR_AUTH_CODESIGN_SPX_KEY": 32,
    "ROT_CREATOR_AUTH_CODESIGN_SPX_KEY_CONFIG": 4,
    "ROT_CREATOR_AUTH_CODESIGN_ECDSA_KEY_TYPE": 4,
    "ROT_CREATOR_AUTH_CODESIGN_ECDSA_KEY": 64,
}

_SPX_KEY_COUNT = 4
_ECDSA_KEY_COUNT = 4

_DIGEST_FIELD_NAME = "ROT_CREATOR_AUTH_CODESIGN_BLOCK_SHA2_256_HASH"


class RotCreatorAuthCodesign:

    def __init__(self, json_data):
        self.json_data = json_data

    def get_key_value(self, item_name: str) -> bytes:
        """Get the value of the item.
        Args:
            item_name: The name of the item to get.
        Returns:
            The value of the item if it exists, otherwise None.
        """
        for partition in self.json_data["partitions"]:
            if partition["name"] == _PARTITION_NAME:
                for item in partition["items"]:
                    if item["name"] == item_name:
                        key_value = item["value"]
                        key_value = key_value[2:] if key_value.startswith(
                            "0x") else key_value
                        key_value = binascii.unhexlify(key_value)
                        return key_value
        return None

    def upsert_key_value(self, item_name: str, value: str):
        """Update the value of the item if it exists, otherwise add a new item.
        Args:
            item_name: The name of the item to update.
            value: The value to update the item with.
        Returns:
            None
        """
        for partition in self.json_data["partitions"]:
            if partition["name"] == _PARTITION_NAME:
                for item in partition["items"]:
                    if item["name"] == item_name:
                        item["value"] = value
                        return
                partition["items"].append({"name": item_name, "value": value})

    def build_key_type_buffer(self, key_items: list[str],
                              num_keys: int) -> bytearray:
        """Build the key type buffer.

        Args:
            key_items: The items to build the buffer from.
            num_keys: The number of keys to build the buffer from.
        Returns:
            The key type buffer.
        """
        key_struct_buffer = bytearray()
        for i in range(num_keys):
            for item in key_items:
                value = self.get_key_value(item + str(i))
                if value is not None:
                    padding_length = _EXPECTED_ITEM_SIZES[item] - len(value)
                    bin_data = b'\x00' * padding_length + value
                else:
                    bin_data = b'\x00' * _EXPECTED_ITEM_SIZES[item]
                reversed_bits = list(bin_data)
                reversed_bits.reverse()
                key_struct_buffer += bytes(reversed_bits)
        return key_struct_buffer

    def build_partition_buffer(self):
        """Build the partition buffer.

        Returns:
            The partition buffer and digest.
        """
        partition_buffer = bytearray()
        partition_buffer += self.build_key_type_buffer(
            _STRUCT_ITEM_NAMES_ECDSA, _ECDSA_KEY_COUNT)
        partition_buffer += self.build_key_type_buffer(_STRUCT_ITEM_NAMES_SPX,
                                                       _SPX_KEY_COUNT)
        digest = SHA256.new(partition_buffer).digest()
        return partition_buffer, bytes(digest)

    def update_json_with_partition_digest(self, digest):
        """Update the JSON with the partition digest.
        Args:
            digest: The digest to update the JSON with.
        Returns:
            None
        """
        self.upsert_key_value(_DIGEST_FIELD_NAME, f"0x{digest.hex()}")


def main():
    parser = argparse.ArgumentParser(
        prog="gen-otp-rot-auth-json",
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('-i',
                        '--input',
                        type=str,
                        metavar='<path>',
                        help='Input JSON file path.')
    parser.add_argument('-o',
                        '--output',
                        type=str,
                        metavar='<path>',
                        help='Output JSON file path.')
    args = parser.parse_args()
    with open(args.input, 'r') as f:
        json_in = hjson.load(f)

    partition_parser = RotCreatorAuthCodesign(json_in)
    partition_buffer, digest = partition_parser.build_partition_buffer()
    partition_parser.update_json_with_partition_digest(digest)

    with open(args.output, 'w') as f:
        f.write(json.dumps(partition_parser.json_data, indent=4))


if __name__ == "__main__":
    main()
