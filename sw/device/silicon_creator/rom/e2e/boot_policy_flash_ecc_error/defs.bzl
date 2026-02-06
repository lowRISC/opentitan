# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

FLASH_ECC_ERROR_CAUSES = [
    {
        "cause": "manifest_security_version",
        "id": 0,
    },
    {
        "cause": "manifest_identifier",
        "id": 1,
    },
    {
        "cause": "manifest_length",
        "id": 2,
    },
    {
        "cause": "manifest_manifest_version",
        "id": 3,
    },
    {
        "cause": "manifest_signed_region_end",
        "id": 4,
    },
    {
        "cause": "manifest_code_start",
        "id": 5,
    },
    {
        "cause": "manifest_code_end",
        "id": 6,
    },
    {
        "cause": "manifest_entry_point",
        "id": 7,
    },
    {
        "cause": "manifest_ecdsa_public_key",
        "id": 8,
    },
    {
        "cause": "manifest_usage_constraints_selector_bits",
        "id": 9,
    },
    {
        "cause": "manifest_ecdsa_signature",
        "id": 10,
    },
    {
        "cause": "manifest_extension_spx_public_key",
        "id": 11,
    },
    {
        "cause": "manifest_extension_spx_signature",
        "id": 12,
    },
    # We only test corrupting the first flash word since this is likely not in
    # the range of test code that needs to execute successfully to drive the
    # test, but still exercising the scenario of a flash corruption happening
    # in the code region.
    {
        "cause": "code_first_word",
        "id": 13,
    },
]

BOOT_POLICY_FLASH_ECC_ERROR_TESTS = [
    {
        "name": "a_corrupt_b_valid_{}",
        "a": ":flash_ecc_self_corruption_slot_a_{}",
        "b": ":uncorrupted_test_slot_b",
        # The regex allows either 8, 9, a in the address, which accomodates the test program
        # being linked as either a ROM_EXT or application normal or coverage builds.
        "exit_success": "Booted slot=0x200[89a]0000; Cause={}",
        # When running under the ROM_EXT, we want to try SlotA first and make sure that
        # we handle the corrupted flash properly.
        "primary": "SlotA",
    },
    {
        "name": "a_valid_b_corrupt_{}",
        "a": ":uncorrupted_test_slot_a",
        "b": ":flash_ecc_self_corruption_slot_b_{}",
        # The regex allows either 0, 1, 2 in the address, which accomodates the test program
        # being linked as either a ROM_EXT or application in normal or coverage builds.
        "exit_success": "Booted slot=0x200[012]0000; Cause={}",
        # When running under the ROM_EXT, we want to try SlotB first and make sure that
        # we handle the corrupted flash properly.
        "primary": "SlotB",
    },
]

SEC_VERS = [
    0,
    1,
]
