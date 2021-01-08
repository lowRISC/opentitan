#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""OTP memory map class, used to create the associated RTL and
documentation, and to create OTP memory images for preloading.
"""

import logging as log
import random
from math import ceil, log2

from tabulate import tabulate
from lib.common import check_bool, check_int

DIGEST_SUFFIX = "_DIGEST"
DIGEST_SIZE = 8


class OtpMemMap():

    # This holds the config dict.
    config = {}

    def __init__(self, config):

        log.info('')
        log.info('Parse and translate OTP memory map.')
        log.info('')

        if "seed" not in config:
            log.error("Missing seed in configuration.")
            exit(1)

        config["seed"] = check_int(config["seed"])

        # Initialize RNG.
        random.seed(int(config['seed']))

        offset = 0
        num_part = 0
        for part in config["partitions"]:
            num_part += 1
            # Defaults
            part.setdefault("offset", offset)
            part.setdefault("name", "unknown_name")
            part.setdefault("variant", "Unbuffered")
            part.setdefault("size", "0")
            part.setdefault("secret", "false")
            part.setdefault("sw_digest", "false")
            part.setdefault("hw_digest", "false")
            part.setdefault("write_lock", "none")
            part.setdefault("read_lock", "none")
            part.setdefault("key_sel", "NoKey")
            log.info("Partition {} at offset {} with size {}".format(
                part["name"], part["offset"], part["size"]))

            # make sure these are boolean types (simplifies the mako templates)
            part["secret"] = check_bool(part["secret"])
            part["sw_digest"] = check_bool(part["sw_digest"])
            part["hw_digest"] = check_bool(part["hw_digest"])
            part["bkout_type"] = check_bool(part["bkout_type"])

            # basic checks
            if part["variant"] not in ["Unbuffered", "Buffered", "LifeCycle"]:
                log.error("Invalid partition type {}".format(part["variant"]))
                exit(1)

            if part["key_sel"] not in [
                    "NoKey", "Secret0Key", "Secret1Key", "Secret2Key"
            ]:
                log.error("Invalid key sel {}".format(part["key_sel"]))
                exit(1)

            if check_bool(part["secret"]) and part["key_sel"] == "NoKey":
                log.error(
                    "A secret partition needs a key select value other than NoKey"
                )
                exit(1)

            if part["write_lock"].lower() not in ["digest", "csr", "none"]:
                log.error("Invalid value for write_lock")
                exit(1)

            if part["read_lock"].lower() not in ["digest", "csr", "none"]:
                log.error("Invalid value for read_lock")
                exit(1)

            if part["sw_digest"] and part["hw_digest"]:
                log.error(
                    "Partition cannot support both a SW and a HW digest at the same time."
                )
                exit(1)

            if part["variant"] == "Unbuffered" and not part["sw_digest"]:
                log.error(
                    "Unbuffered partitions without digest are not supported at the moment."
                )
                exit(1)

            if not part["sw_digest"] and not part["hw_digest"]:
                if part["write_lock"].lower(
                ) == "digest" or part["read_lock"].lower() == "digest":
                    log.error(
                        "A partition can only be write/read lockable if it has a hw or sw digest."
                    )
                    exit(1)

            if check_int(part["offset"]) % 8:
                log.error("Partition offset must be 64bit aligned")
                exit(1)

            if check_int(part["size"]) % 8:
                log.error("Partition size must be 64bit aligned")
                exit(1)

            # Loop over items within a partition
            for item in part["items"]:
                item.setdefault("name", "unknown_name")
                item.setdefault("size", "0")
                item.setdefault("isdigest", "false")
                item.setdefault("offset", offset)
                # Generate random constant to be used when partition has
                # not been initialized yet or when it is in error state.
                if check_bool(item.setdefault("rand_inv_default", "false")):
                    inv_default = random.getrandbits(
                        check_int(item["size"]) * 8)
                else:
                    inv_default = 0
                item.setdefault(
                    "inv_default", "{}'h{:0X}".format(
                        check_int(item["size"]) * 8, inv_default))
                log.info("> Item {} at offset {} with size {}".format(
                    item["name"], offset, item["size"]))
                offset += check_int(item["size"])

            # Place digest at the end of a partition.
            if part["sw_digest"] or part["hw_digest"]:
                part["items"].append({
                    "name":
                    part["name"] + DIGEST_SUFFIX,
                    "size":
                    DIGEST_SIZE,
                    "offset":
                    check_int(part["offset"]) + check_int(part["size"]) -
                    DIGEST_SIZE,
                    "isdigest":
                    "True",
                    "inv_default":
                    "{256{1'b1}}"
                })

                log.info("> Adding digest {} at offset {} with size {}".format(
                    part["name"] + DIGEST_SUFFIX, offset, DIGEST_SIZE))
                offset += DIGEST_SIZE

            if len(part["items"]) == 0:
                log.warning("Partition does not contain any items.")

            # check offsets and size
            if offset > check_int(part["offset"]) + check_int(part["size"]):
                log.error("Not enough space in partitition "
                          "{} to accommodate all items. Bytes available "
                          "= {}, bytes requested = {}".format(
                              part["name"], part["size"],
                              offset - part["offset"]))
                exit(1)

            offset = check_int(part["offset"]) + check_int(part["size"])

        otp_size = check_int(config["otp"]["depth"]) * check_int(
            config["otp"]["width"])
        config["otp"]["size"] = otp_size
        config["otp"]["addr_width"] = ceil(
            log2(check_int(config["otp"]["depth"])))
        config["otp"]["byte_addr_width"] = ceil(log2(check_int(otp_size)))

        if offset > otp_size:
            log.error(
                "OTP is not big enough to store all partitions. "
                "Bytes available {}, bytes required {}",
                otp_size, offset)
            exit(1)

        log.info("Total number of partitions: {}".format(num_part))
        log.info("Bytes available in OTP: {}".format(otp_size))
        log.info("Bytes required for partitions: {}".format(offset))

        self.config = config

        log.info('')
        log.info('Successfully parsed and translated OTP memory map.')
        log.info('')


    def create_partitions_table(self):
        header = [
            "Partition", "Secret", "Buffered", "WR Lockable", "RD Lockable",
            "Description"
        ]
        table = [header]
        colalign = ("center", ) * len(header)

        for part in self.config["partitions"]:
            is_secret = "yes" if check_bool(part["secret"]) else "no"
            is_buffered = "yes" if part["variant"] in [
                "Buffered", "LifeCycle"
            ] else "no"
            wr_lockable = "no"
            if part["write_lock"].lower() in ["csr", "digest"]:
                wr_lockable = "yes (" + part["write_lock"] + ")"
            rd_lockable = "no"
            if part["read_lock"].lower() in ["csr", "digest"]:
                rd_lockable = "yes (" + part["read_lock"] + ")"
            # remove newlines
            desc = ' '.join(part["desc"].split())
            row = [
                part["name"], is_secret, is_buffered, wr_lockable, rd_lockable,
                desc
            ]
            table.append(row)

        return tabulate(table,
                        headers="firstrow",
                        tablefmt="pipe",
                        colalign=colalign)

    def create_mmap_table(self):
        header = [
            "Index", "Partition", "Size [B]", "Access Granule", "Item",
            "Byte Address", "Size [B]"
        ]
        table = [header]
        colalign = ("center", ) * len(header)

        for k, part in enumerate(self.config["partitions"]):
            for j, item in enumerate(part["items"]):
                granule = "64bit" if check_bool(part["secret"]) else "32bit"

                if check_bool(item["isdigest"]):
                    granule = "64bit"
                    name = "[{}](#Reg_{}_0)".format(item["name"],
                                                    item["name"].lower())
                else:
                    name = item["name"]

                if j == 0:
                    row = [str(k), part["name"], str(part["size"]), granule]
                else:
                    row = ["", "", "", granule]

                row.extend([
                    name, "0x{:03X}".format(check_int(item["offset"])),
                    str(item["size"])
                ])

                table.append(row)

        return tabulate(table,
                        headers="firstrow",
                        tablefmt="pipe",
                        colalign=colalign)

    def create_digests_table(self):
        header = ["Digest Name", " Affected Partition", "Calculated by HW"]
        table = [header]
        colalign = ("center", ) * len(header)

        for part in self.config["partitions"]:
            if check_bool(part["hw_digest"]) or check_bool(part["sw_digest"]):
                is_hw_digest = "yes" if check_bool(part["hw_digest"]) else "no"
                for item in part["items"]:
                    if check_bool(item["isdigest"]):
                        name = "[{}](#Reg_{}_0)".format(
                            item["name"], item["name"].lower())
                        row = [name, part["name"], is_hw_digest]
                        table.append(row)
                        break
                else:
                    log.error(
                        "Partition with digest does not contain a digest item")
                    exit(1)

        return tabulate(table,
                        headers="firstrow",
                        tablefmt="pipe",
                        colalign=colalign)
