# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from sw.host.penetrationtests.python.fi.communication.fi_sym_cryptolib_commands import (
    OTFISymCrypto,
)
from python.runfiles import Runfiles
from sw.host.penetrationtests.python.util import targets
import json
import unittest
import argparse
import sys
import os

opentitantool_path = ""
target = None

# Read in the extra arguments from the opentitan_test.
parser = argparse.ArgumentParser()
parser.add_argument("--bitstream", type=str)
parser.add_argument("--bootstrap", type=str)
parser.add_argument("--data_size", type=int, default=640000)

args, config_args = parser.parse_known_args()

BITSTREAM = args.bitstream
BOOTSTRAP = args.bootstrap

OUTPUT_DIR_VAR = "TEST_UNDECLARED_OUTPUTS_DIR"
output_dir = None


class CCRngTest(unittest.TestCase):
    def test_drbg_output(self):
        # Absolute file path
        output_file_path = os.path.join(output_dir, "cc_drbg_output.bin")

        symfi = OTFISymCrypto(target)
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()

        print()
        print(
            "Starting the DRBG output test for CC, the following is the chip state",
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
            cryptolib_version,
        ) = symfi.init()
        print(device_id)
        print(sensors)
        print(alerts)
        print(owner_page)
        print(boot_log)
        print(boot_measurements)
        print(version)
        print(cryptolib_version)

        print()
        print("Performing the cryptolib TRNG init", flush=True)
        print()
        symfi.handle_trng_init(0, 0, 0)
        response = target.read_response()
        response_dict = json.loads(response)
        self.assertEqual(
            response_dict["status"],
            0,
            f"Status error in handle_trng_init: {response}",
        )
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
        print(response)

        print(
            "Calling the DRBG reseed without personalization",
            flush=True,
        )
        symfi.handle_drbg_reseed([], 0, [], 0, 0, 0, 0, 0)
        response = target.read_response()
        response_dict = json.loads(response)
        self.assertEqual(
            response_dict["status"],
            0,
            f"Status error in handle_drbg_reseed: {response}",
        )
        self.assertEqual(
            response_dict["err_status"],
            0,
            f"Error status in handle_drbg_reseed: {response}",
        )
        self.assertEqual(
            response_dict["loc_alerts"],
            0,
            f"Local alerts in handle_drbg_reseed: {response}",
        )
        alerts = response_dict["alerts"]
        all_alerts_zero = all(alert == 0 for alert in alerts)
        self.assertTrue(
            all_alerts_zero,
            f"Alerts in handle_drbg_reseed: {response}",
        )
        ast_alerts = response_dict["ast_alerts"]
        all_ast_alerts_zero = all(alert == 0 for alert in ast_alerts)
        self.assertTrue(
            all_ast_alerts_zero,
            f"AST alerts in handle_drbg_reseed: {response}",
        )
        print(response)

        DRBGSIZE = args.data_size // 256

        print(
            f"We write a total of {DRBGSIZE} times 256 bytes of data.",
            flush=True,
        )
        iterations = DRBGSIZE
        with open(output_file_path, "wb") as f:
            for _ in range(iterations):
                # Generate 256 bytes of data (the max output size)
                symfi.handle_drbg_generate([0], 0, 256, 0, 0, 0)
                response = target.read_response()
                response_dict = json.loads(response)
                self.assertEqual(
                    response_dict["status"],
                    0,
                    f"Status error in handle_drbg_generate: {response}",
                )
                self.assertEqual(
                    response_dict["err_status"],
                    0,
                    f"Error status in handle_drbg_generate: {response}",
                )
                self.assertEqual(
                    response_dict["loc_alerts"],
                    0,
                    f"Local alerts in handle_drbg_generate: {response}",
                )
                alerts = response_dict["alerts"]
                all_alerts_zero = all(alert == 0 for alert in alerts)
                self.assertTrue(
                    all_alerts_zero,
                    f"Alerts in handle_drbg_generate: {response}",
                )
                ast_alerts = response_dict["ast_alerts"]
                all_ast_alerts_zero = all(alert == 0 for alert in ast_alerts)
                self.assertTrue(
                    all_ast_alerts_zero,
                    f"AST alerts in handle_drbg_generate: {response}",
                )
                data_list = response_dict["data"]
                binary_data = bytes(data_list)
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
