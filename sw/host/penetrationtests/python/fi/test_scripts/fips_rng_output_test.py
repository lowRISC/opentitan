# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from sw.host.penetrationtests.python.fi.communication.fi_rng_commands import (
    OTFIRng,
)
from python.runfiles import Runfiles
from sw.host.penetrationtests.python.util import targets
import json
import unittest
import argparse
import sys
import os
import struct

opentitantool_path = ""
target = None

# Read in the extra arguments from the opentitan_test.
parser = argparse.ArgumentParser()
parser.add_argument("--bitstream", type=str)
parser.add_argument("--bootstrap", type=str)
parser.add_argument("--fips_rng_reset", action="store_true")

args, config_args = parser.parse_known_args()

BITSTREAM = args.bitstream
BOOTSTRAP = args.bootstrap
RESET = args.fips_rng_reset

OUTPUT_DIR_VAR = "TEST_UNDECLARED_OUTPUTS_DIR"
output_dir = None


class FipsRngTest(unittest.TestCase):
    def test_fips_rng(self):
        filename = "fips_rng_output.bin"
        if RESET:
            filename = "fips_rng_reset_output.bin"
        # Absolute file path
        output_file_path = os.path.join(output_dir, filename)

        rng = OTFIRng(target)
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()

        print()
        print(
            "Starting the FIPS rng output test, the following is the chip state",
            flush=True,
        )
        print()
        (
            device_id,
            sensors,
            alerts,
            owner_page,
            boot_log,
            boot_measurements,
            version,
        ) = rng.init("char_fw_overwrite")
        print(device_id)
        print(sensors)
        print(alerts)
        print(owner_page)
        print(boot_log)
        print(boot_measurements)
        print(version)

        print()
        print(
            "Getting 1024 instances of FW OV RNG data giving 1024 samples each",
            flush=True,
        )
        print()
        if RESET:
            print("Performing with resets between each instance", flush=True)
            print()

        with open(output_file_path, "wb") as f:
            for i in range(1024):
                if RESET:
                    target.reset_target()
                    # Clear the output from the reset
                    target.dump_all()

                    (
                        device_id,
                        sensors,
                        alerts,
                        owner_page,
                        boot_log,
                        boot_measurements,
                        version,
                    ) = rng.init("char_fw_overwrite")

                # We require 1024 samples per loop, but each sample is 4 bits large
                for _ in range(4):
                    rng.rng_fw_overwrite(disable_health_check=True)
                    response = target.read_response()
                    response_dict = json.loads(response)
                    self.assertEqual(
                        response_dict["err_status"],
                        0,
                        f"Error status in handle_trng_init: {response}",
                    )
                    self.assertEqual(
                        response_dict["loc_alerts"],
                        0,
                        f"Local alerts in handle_trng_init: {response}",
                    )
                    alerts = response_dict["alerts"]
                    all_alerts_zero = all(alert == 0 for alert in alerts)
                    self.assertTrue(
                        all_alerts_zero,
                        f"Alerts in handle_trng_init: {response}",
                    )
                    ast_alerts = response_dict["ast_alerts"]
                    all_ast_alerts_zero = all(alert == 0 for alert in ast_alerts)
                    self.assertTrue(
                        all_ast_alerts_zero,
                        f"AST alerts in handle_trng_init: {response}",
                    )
                    data_list = response_dict["rand"]
                    binary_data = struct.pack("<" + "I" * len(data_list), *data_list)
                    f.write(binary_data)
        print("Data is logged in ", output_file_path)
        print()
        print()


if __name__ == "__main__":
    r = Runfiles.Create()

    # Set the output directory as test output
    output_dir = os.environ.get("TEST_UNDECLARED_OUTPUTS_DIR")
    # Get the opentitantool path.
    opentitantool_path = r.Rlocation(
        "lowrisc_opentitan/sw/host/opentitantool/opentitantool"
    )
    # Program the bitstream for FPGAs.
    bitstream_path = None
    if BITSTREAM:
        bitstream_path = r.Rlocation("lowrisc_opentitan/" + BITSTREAM)
    # Get the firmware path.
    firmware_path = r.Rlocation("lowrisc_opentitan/" + BOOTSTRAP)

    if "fpga" in BOOTSTRAP:
        target_type = "fpga"
    else:
        target_type = "chip"

    target_cfg = targets.TargetConfig(
        target_type=target_type,
        interface_type="hyperdebug",
        fw_bin=firmware_path,
        opentitantool=opentitantool_path,
        bitstream=bitstream_path,
        tool_args=config_args,
    )

    target = targets.Target(target_cfg)

    target.initialize_target()

    unittest.main(argv=[sys.argv[0]])
