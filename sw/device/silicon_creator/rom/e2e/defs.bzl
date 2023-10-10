# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:const.bzl", "CONST")
load("//rules:opentitan.bzl", "SILICON_CREATOR_KEYS")

MSG_TEMPLATE_BFV = "{}{}\r\n(?s:.*){}{}\r\n".format(
    CONST.SHUTDOWN.PREFIX.BFV,
    "{0}",
    CONST.SHUTDOWN.PREFIX.BFV,
    "{0}",
)

MSG_TEMPLATE_BFV_LCV = "{}{}\r\n{}{}\r\n(?s:.*){}{}\r\n{}{}\r\n".format(
    CONST.SHUTDOWN.PREFIX.BFV,
    "{0}",
    CONST.SHUTDOWN.PREFIX.LCV,
    "{1}",
    CONST.SHUTDOWN.PREFIX.BFV,
    "{0}",
    CONST.SHUTDOWN.PREFIX.LCV,
    "{1}",
)

MSG_STARTING_ROM_EXT = "Starting ROM_EXT"

MSG_PASS = "PASS!"

SLOTS = {
    "a": "0x0",
    "b": "0x80000",
}

# list of keys that will be used to build various flash images
# it must contain at least one key of each type and contains all
# the keys used in SIGVERIFY_LCS_2_VALID_KEY
SIGVERIFY_LC_KEYS = [
    SILICON_CREATOR_KEYS.FAKE.RSA.TEST[0].name,
    SILICON_CREATOR_KEYS.FAKE.RSA.DEV[0].name,
    SILICON_CREATOR_KEYS.FAKE.RSA.PROD[0].name,
]
