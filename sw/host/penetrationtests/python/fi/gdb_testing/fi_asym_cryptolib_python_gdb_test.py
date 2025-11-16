# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# What to do when running into errors:
# - If device is busy or seeing "rejected 'gdb' connection, no more connections allowed",
# cut the USB connection, e.g., sudo fuser /dev/ttyUSB0 and kill the PID
# - If the port is busy check sudo lsof -i :3333 and then kill the PID

from sw.host.penetrationtests.python.fi.communication.fi_asym_cryptolib_commands import (
    OTFIAsymCrypto,
)
from python.runfiles import Runfiles
from sw.host.penetrationtests.python.util import targets
from sw.host.penetrationtests.python.util import common_library
from sw.host.penetrationtests.python.util.gdb_controller import GDBController
from sw.host.penetrationtests.python.util.dis_parser import DisParser
from collections import Counter
import json
import argparse
import unittest
import sys
import os
import time
from Crypto.PublicKey import RSA, ECC
from Crypto.Signature import pkcs1_15, DSS
from Crypto.Hash import SHA256, SHA384

ignored_keys_set = set(["status"])
opentitantool_path = ""
log_dir = ""
elf_path = ""

# We set to only apply instruction skips in the first
# MAX_SKIPS_PER_LOOP iterations of a loop
MAX_SKIPS_PER_LOOP = 3

target = None
asymfi = None

# Read in the extra arguments from the opentitan_test.
parser = argparse.ArgumentParser()
parser.add_argument("--bitstream", type=str)
parser.add_argument("--bootstrap", type=str)

args, config_args = parser.parse_known_args()

BITSTREAM = args.bitstream
BOOTSTRAP = args.bootstrap

original_stdout = sys.stdout


class AsymCryptolibFiSim(unittest.TestCase):
    def test_p384_verify(self):
        print("Starting the p384 verify test")
        # Preparing the input for an invalid signature
        key = ECC.generate(curve="P-384")
        pubx = [x for x in key.pointQ.x.to_bytes(48, "little")]
        puby = [x for x in key.pointQ.y.to_bytes(48, "little")]
        message = [i for i in range(16)]
        signer = DSS.new(key, "fips-186-3")
        h = SHA384.new(bytes(message))
        signature = [x for x in signer.sign(h)]
        # Corrupt the signature for FiSim Testing
        signature[0] ^= 0x1
        r_bytes = signature[:48]
        s_bytes = signature[48:]
        r_bytes.reverse()
        s_bytes.reverse()
        cfg = 0
        trigger = 1
        h = SHA384.new(bytes(message))
        message_digest = [x for x in h.digest()]

        # Directory for the trace log files
        pc_trace_file = os.path.join(log_dir, "p384_verify_pc_trace.log")
        # Directory for the output results
        test_results_file = os.path.join(log_dir, "p384_verify_test_results.log")
        # Directory for the the log of the campaign
        campaign_file = os.path.join(log_dir, "p384_verify_test_campaign.log")

        successful_faults = 0
        total_attacks = 0

        def trigger_testos_init(print_output=True):
            # Initializing the testOS (setting up the alerts and accelerators)
            (device_id, _, _, _, _, _, _) = asymfi.init(
                alert_config=common_library.no_escalation_alert_config
            )
            if print_output:
                print("Output from init ", device_id)

        def read_testos_output():
            # Read the output from the operation
            response = target.read_response(max_tries=1000)
            return response

        def reset_gdb(gdb):
            gdb.close_gdb()
            gdb = GDBController(
                gdb_path=GDB_PATH,
                gdb_port=GDB_PORT,
                elf_file=elf_path,
            )
            return gdb

        def reset_target_and_gdb(gdb):
            gdb.close_gdb()
            gdb = GDBController(
                gdb_path=GDB_PATH,
                gdb_port=GDB_PORT,
                elf_file=elf_path,
            )
            gdb.reset_target()
            target.dump_all()
            trigger_testos_init(print_output=False)
            # Reset again
            gdb.close_gdb()
            gdb = GDBController(
                gdb_path=GDB_PATH,
                gdb_port=GDB_PORT,
                elf_file=elf_path,
            )
            return gdb

        def re_initialize(gdb):
            gdb.close_gdb()
            target.close_openocd()
            target.initialize_target()
            trigger_testos_init()
            target.dump_all()
            gdb = GDBController(gdb_path=GDB_PATH, gdb_port=GDB_PORT, elf_file=elf_path)
            return gdb

        gdb = None
        started = False
        with open(test_results_file, "w") as test_results, open(campaign_file, "w") as campaign:
            print(f"Switching terminal output to {campaign_file}", flush=True)
            sys.stdout = campaign
            try:
                # Program the bitstream, flash the target, and set up OpenOCD
                target.initialize_target()

                # Initialize the testOS
                trigger_testos_init()

                # Connect to GDB
                gdb = GDBController(gdb_path=GDB_PATH, gdb_port=GDB_PORT, elf_file=elf_path)

                # We provide the name of the unique marker in the pentest framework
                function_name = "PENTEST_MARKER_P384_VERIFY"
                # Gives back an array of hits where the function is called
                trace_address = parser.get_marker_addresses(function_name)
                print("Start and stop addresses of ", function_name, ": ", trace_address)

                crash_observation_address = parser.get_function_start_address(
                    "ottf_exception_handler"
                )

                # Start the tracing
                # We set a short timeout to detect whether GDB has connected properly
                # and a long timeout for the entire tracing
                initial_timeout = 10
                total_timeout = 60 * 60 * 5

                gdb.setup_pc_trace(pc_trace_file, trace_address[0], trace_address[1])
                gdb.send_command("c", check_response=False)

                # Trigger the p384 verify from the testOS (we do not read its output)
                asymfi.handle_p384_verify(
                    pubx, puby, r_bytes, s_bytes, message_digest, cfg, trigger
                )

                start_time = time.time()
                initial_timeout_stopped = False
                total_timeout_stopped = False

                # Run the tracing to get the trace log
                while time.time() - start_time < initial_timeout:
                    output = gdb.read_output()
                    if "breakpoint 1, " in output:
                        initial_timeout_stopped = True
                        break
                if not initial_timeout_stopped:
                    print("No initial break point found, can be a misfire, try again")
                    sys.exit(1)
                while time.time() - start_time < total_timeout:
                    output = gdb.read_output()
                    if "PC trace complete" in output:
                        print("\nTrace complete")
                        total_timeout_stopped = True
                        break
                if not total_timeout_stopped:
                    print("Final tracing timeout reached")
                    sys.exit(1)

                # Parse and truncate the trace log to get all PCs in a list
                pc_list = gdb.parse_pc_trace_file(pc_trace_file)
                # Get the unique PCs and annotate their occurence count
                pc_count_dict = Counter(pc_list)
                if len(pc_count_dict) <= 0:
                    print("Found no tracing, stopping")
                    sys.exit(1)
                print("Tracing has a total of", len(pc_count_dict), "unique PCs", flush=True)

                # Reset the target, flush the output, and close gdb
                gdb = re_initialize(gdb)

                started = True
                for pc, count in pc_count_dict.items():
                    for i_count in range(min(MAX_SKIPS_PER_LOOP, count)):
                        print("-" * 80)
                        print("Applying instruction skip in ", pc, "occurence", i_count)
                        print("-" * 80)

                        crash_observation = "crash detected"

                        try:
                            # The observation points
                            observations = {
                                # Crash check
                                crash_observation_address: f"{crash_observation}",
                            }
                            gdb.add_observation(observations)

                            gdb.apply_instruction_skip(
                                pc, parser.parse_next_instruction(pc), i_count
                            )
                            gdb.send_command("c", check_response=False)

                            # The instruction skip loop
                            asymfi.handle_p384_verify(
                                pubx, puby, r_bytes, s_bytes, message_digest, cfg, trigger
                            )
                            testos_response = read_testos_output()

                            gdb_response = gdb.read_output()
                            if "instruction skip applied" in gdb_response:
                                total_attacks += 1

                                if crash_observation in gdb_response:
                                    print("Crash detected, resetting", flush=True)
                                    gdb = reset_target_and_gdb(gdb)
                                else:
                                    testos_response_json = json.loads(testos_response)
                                    print("Output:", testos_response_json, flush=True)
                                    verification_result = testos_response_json["result"]
                                    verification_status = testos_response_json["status"]
                                    if verification_result and (verification_status == 0):
                                        successful_faults += 1
                                        print("-" * 80)
                                        print("Successful FI attack!")
                                        print("Location:", pc, "iteration", i_count)
                                        print(gdb_response)
                                        print("Response:", testos_response_json)
                                        print("-" * 80)
                                        test_results.write(
                                            f"{pc}, {i_count}: {testos_response_json}\n"
                                        )
                                    # Reset GDB by closing and opening again
                                    gdb = reset_gdb(gdb)
                                    # We do not need to reset the target since it gave an output
                            else:
                                print("No break point found, something went wrong", flush=True)
                                gdb = re_initialize(gdb)

                        except json.JSONDecodeError:
                            print(
                                "Error: JSON decoding failed. Invalid response format",
                                flush=True,
                            )
                            try:
                                gdb = reset_target_and_gdb(gdb)
                            except TimeoutError:
                                gdb = re_initialize(gdb)

                        except TimeoutError as e:
                            print("Timeout error, retrying", flush=True)
                            print(e, flush=True)
                            try:
                                gdb = reset_target_and_gdb(gdb)
                            except TimeoutError:
                                gdb = re_initialize(gdb)

            finally:
                print("-" * 80)
                print("Trace data is logged in ", pc_trace_file)
                print("The campaign is logged in ", campaign_file)
                print("Instruction skip results are logged in ", test_results_file)
                print(f"Total attacks {total_attacks}, successful attacks {successful_faults}")
                print("You can find the dissassembly in ", dis_path)
                # Close the OpenOCD and GDB connection at the end
                if gdb:
                    gdb.close_gdb()
                target.close_openocd()
                test_results.write(
                    f"Total attacks {total_attacks}, successful attacks {successful_faults}\n"
                )
                sys.stdout = original_stdout
                print("Trace data is logged in ", pc_trace_file)
                print("The campaign is logged in ", campaign_file)
                print("Instruction skip results are logged in ", test_results_file)
                print(f"Total attacks {total_attacks}, successful attacks {successful_faults}")
                print("You can find the dissassembly in ", dis_path)
                self.assertEqual(successful_faults, 0)
                self.assertEqual(started, True)

    def test_p384_ecdh(self):
        print("Starting the p384 ecdh test")
        # Preparing the input for an invalid signature
        private_key1 = ECC.generate(curve="P-384")
        private_key_array1 = [x for x in private_key1.d.to_bytes(48, "little")]
        private_key2 = ECC.generate(curve="P-384")
        private_key_array2 = [x for x in private_key2.d.to_bytes(48, "little")]
        private_key_array = [private_key_array1, private_key_array2]
        key = ECC.generate(curve="P-384")
        public_point = key.pointQ
        public_x = [x for x in public_point.x.to_bytes(48, "little")]
        public_y = [x for x in public_point.y.to_bytes(48, "little")]
        cfg = 0
        trigger = 0

        # Directory for the trace log files
        pc_trace_file = os.path.join(log_dir, "p384_ecdh_pc_trace.log")
        # Directory for the output results
        test_results_file = os.path.join(log_dir, "p384_ecdh_test_results.log")
        # Directory for the the log of the campaign
        campaign_file = os.path.join(log_dir, "p384_ecdh_test_campaign.log")

        successful_faults = 0
        total_attacks = 0

        def trigger_testos_init(print_output=True):
            # Initializing the testOS (setting up the alerts and accelerators)
            (device_id, _, _, _, _, _, _) = asymfi.init(
                alert_config=common_library.no_escalation_alert_config
            )
            if print_output:
                print("Output from init ", device_id)

        def read_testos_output():
            # Read the output from the operation
            response = target.read_response(max_tries=1000)
            return response

        def reset_gdb(gdb):
            gdb.close_gdb()
            gdb = GDBController(
                gdb_path=GDB_PATH,
                gdb_port=GDB_PORT,
                elf_file=elf_path,
            )
            return gdb

        def reset_target_and_gdb(gdb):
            gdb.close_gdb()
            gdb = GDBController(
                gdb_path=GDB_PATH,
                gdb_port=GDB_PORT,
                elf_file=elf_path,
            )
            gdb.reset_target()
            target.dump_all()
            trigger_testos_init(print_output=False)
            # Reset again
            gdb.close_gdb()
            gdb = GDBController(
                gdb_path=GDB_PATH,
                gdb_port=GDB_PORT,
                elf_file=elf_path,
            )
            gdb.dump_output()
            target.dump_all()
            return gdb

        def re_initialize(gdb):
            gdb.close_gdb()
            target.close_openocd()
            target.initialize_target()
            trigger_testos_init()
            target.dump_all()
            gdb = GDBController(gdb_path=GDB_PATH, gdb_port=GDB_PORT, elf_file=elf_path)
            return gdb

        ecdh_output = [None, None]

        gdb = None
        started = False
        with open(test_results_file, "w") as test_results, open(campaign_file, "w") as campaign:
            print(f"Switching terminal output to {campaign_file}", flush=True)
            sys.stdout = campaign
            try:
                # Program the bitstream, flash the target, and set up OpenOCD
                target.initialize_target()

                # Initialize the testOS
                trigger_testos_init()

                # Connect to GDB
                gdb = GDBController(gdb_path=GDB_PATH, gdb_port=GDB_PORT, elf_file=elf_path)

                # We provide the name of the unique marker in the pentest framework
                function_name = "PENTEST_MARKER_P384_ECDH"
                # Gives back an array of hits where the function is called
                trace_address = parser.get_marker_addresses(function_name)
                print("Start and stop addresses of ", function_name, ": ", trace_address)

                crash_observation_address = parser.get_function_start_address(
                    "ottf_exception_handler"
                )

                # Start the tracing
                # We set a short timeout to detect whether GDB has connected properly
                # and a long timeout for the entire tracing
                initial_timeout = 10
                total_timeout = 60 * 60 * 5

                gdb.setup_pc_trace(pc_trace_file, trace_address[0], trace_address[1])
                gdb.send_command("c", check_response=False)

                # Trigger the p384 verify from the testOS (we do not read its output)
                asymfi.handle_p384_ecdh(private_key_array[0], public_x, public_y, cfg, trigger)

                start_time = time.time()
                initial_timeout_stopped = False
                total_timeout_stopped = False

                # Run the tracing to get the trace log
                while time.time() - start_time < initial_timeout:
                    output = gdb.read_output()
                    if "breakpoint 1, " in output:
                        initial_timeout_stopped = True
                        break
                if not initial_timeout_stopped:
                    print("No initial break point found, can be a misfire, try again")
                    sys.exit(1)
                while time.time() - start_time < total_timeout:
                    output = gdb.read_output()
                    if "PC trace complete" in output:
                        print("\nTrace complete")
                        total_timeout_stopped = True
                        break
                if not total_timeout_stopped:
                    print("Final tracing timeout reached")
                    sys.exit(1)

                # Parse and truncate the trace log to get all PCs in a list
                pc_list = gdb.parse_pc_trace_file(pc_trace_file)
                # Get the unique PCs and annotate their occurence count
                pc_count_dict = Counter(pc_list)
                if len(pc_count_dict) <= 0:
                    print("Found no tracing, stopping")
                    sys.exit(1)
                print("Tracing has a total of", len(pc_count_dict), "unique PCs", flush=True)

                # Reset the target, flush the output, and close gdb
                gdb = re_initialize(gdb)

                started = True
                for pc, count in pc_count_dict.items():
                    for i_count in range(min(MAX_SKIPS_PER_LOOP, count)):
                        # Search for collisions in outputs between the ecdh instances
                        for i in range(2):
                            print("-" * 80)
                            print("Applying instruction skip in ", pc, "occurence", i_count)
                            print("-" * 80)

                            crash_observation = "crash detected"

                            try:
                                # The observation points
                                observations = {
                                    # Crash check
                                    crash_observation_address: f"{crash_observation}",
                                }
                                gdb.add_observation(observations)

                                gdb.apply_instruction_skip(
                                    pc, parser.parse_next_instruction(pc), i_count
                                )
                                gdb.send_command("c", check_response=False)

                                # The instruction skip loop
                                asymfi.handle_p384_ecdh(
                                    private_key_array[i], public_x, public_y, cfg, trigger
                                )
                                testos_response = read_testos_output()

                                gdb_response = gdb.read_output()
                                if "instruction skip applied" in gdb_response:
                                    total_attacks += 1

                                    if crash_observation in gdb_response:
                                        print("Crash detected, resetting", flush=True)
                                        gdb = reset_target_and_gdb(gdb)
                                    else:
                                        testos_response_json = json.loads(testos_response)
                                        print("Output:", testos_response_json, flush=True)
                                        if testos_response_json["status"] == 0:
                                            ecdh_output[i] = testos_response_json["shared_key"]
                                            if ecdh_output[i] == ecdh_output[1 - i]:
                                                successful_faults += 1
                                                print("-" * 80)
                                                print("Successful FI attack!")
                                                print("Location:", pc, "iteration", i_count)
                                                print(gdb_response)
                                                print("Response:", testos_response_json)
                                                print("-" * 80)
                                                test_results.write(
                                                    f"{pc}, {i_count}: {testos_response_json}\n"
                                                )
                                        # Reset GDB by closing and opening again
                                        gdb = reset_gdb(gdb)
                                        # We do not need to reset the target since it gave an output
                                else:
                                    print("No break point found, something went wrong", flush=True)
                                    gdb = re_initialize(gdb)

                            except json.JSONDecodeError:
                                print(
                                    "Error: JSON decoding failed. Invalid response format",
                                    flush=True,
                                )
                                try:
                                    gdb = reset_target_and_gdb(gdb)
                                except TimeoutError:
                                    gdb = re_initialize(gdb)

                            except TimeoutError as e:
                                print("Timeout error, retrying", flush=True)
                                print(e, flush=True)
                                try:
                                    gdb = reset_target_and_gdb(gdb)
                                except TimeoutError:
                                    gdb = re_initialize(gdb)

            finally:
                print("-" * 80)
                print("Trace data is logged in ", pc_trace_file)
                print("The campaign is logged in ", campaign_file)
                print("Instruction skip results are logged in ", test_results_file)
                print(f"Total attacks {total_attacks}, successful attacks {successful_faults}")
                print("You can find the dissassembly in ", dis_path)
                # Close the OpenOCD and GDB connection at the end
                if gdb:
                    gdb.close_gdb()
                target.close_openocd()
                test_results.write(
                    f"Total attacks {total_attacks}, successful attacks {successful_faults}\n"
                )
                sys.stdout = original_stdout
                print("Trace data is logged in ", pc_trace_file)
                print("The campaign is logged in ", campaign_file)
                print("Instruction skip results are logged in ", test_results_file)
                print(f"Total attacks {total_attacks}, successful attacks {successful_faults}")
                print("You can find the dissassembly in ", dis_path)
                self.assertEqual(successful_faults, 0)
                self.assertEqual(started, True)

    def test_p256_verify(self):
        print("Starting the p256 verify test")
        # Preparing the input for an invalid signature
        key = ECC.generate(curve="P-256")
        pubx = [x for x in key.pointQ.x.to_bytes(32, "little")]
        puby = [x for x in key.pointQ.y.to_bytes(32, "little")]
        message = [i for i in range(16)]
        signer = DSS.new(key, "fips-186-3")
        h = SHA256.new(bytes(message))
        signature = [x for x in signer.sign(h)]
        # Corrupt the signature for FiSim Testing
        signature[0] ^= 0x1
        r_bytes = signature[:32]
        s_bytes = signature[32:]
        r_bytes.reverse()
        s_bytes.reverse()
        cfg = 0
        trigger = 1
        h = SHA256.new(bytes(message))
        message_digest = [x for x in h.digest()]

        # Directory for the trace log files
        pc_trace_file = os.path.join(log_dir, "p256_verify_pc_trace.log")
        # Directory for the output results
        test_results_file = os.path.join(log_dir, "p256_verify_test_results.log")
        # Directory for the the log of the campaign
        campaign_file = os.path.join(log_dir, "p256_verify_test_campaign.log")

        successful_faults = 0
        total_attacks = 0

        def trigger_testos_init(print_output=True):
            # Initializing the testOS (setting up the alerts and accelerators)
            (device_id, _, _, _, _, _, _) = asymfi.init(
                alert_config=common_library.no_escalation_alert_config
            )
            if print_output:
                print("Output from init ", device_id)

        def read_testos_output():
            # Read the output from the operation
            response = target.read_response(max_tries=1000)
            return response

        def reset_gdb(gdb):
            gdb.close_gdb()
            gdb = GDBController(
                gdb_path=GDB_PATH,
                gdb_port=GDB_PORT,
                elf_file=elf_path,
            )
            return gdb

        def reset_target_and_gdb(gdb):
            gdb.close_gdb()
            gdb = GDBController(
                gdb_path=GDB_PATH,
                gdb_port=GDB_PORT,
                elf_file=elf_path,
            )
            gdb.reset_target()
            target.dump_all()
            trigger_testos_init(print_output=False)
            # Reset again
            gdb.close_gdb()
            gdb = GDBController(
                gdb_path=GDB_PATH,
                gdb_port=GDB_PORT,
                elf_file=elf_path,
            )
            gdb.dump_output()
            target.dump_all()
            return gdb

        def re_initialize(gdb):
            gdb.close_gdb()
            target.close_openocd()
            target.initialize_target()
            trigger_testos_init()
            target.dump_all()
            gdb = GDBController(gdb_path=GDB_PATH, gdb_port=GDB_PORT, elf_file=elf_path)
            return gdb

        gdb = None
        started = False
        with open(test_results_file, "w") as test_results, open(campaign_file, "w") as campaign:
            print(f"Switching terminal output to {campaign_file}", flush=True)
            sys.stdout = campaign
            try:
                # Program the bitstream, flash the target, and set up OpenOCD
                target.initialize_target()

                # Initialize the testOS
                trigger_testos_init()

                # Connect to GDB
                gdb = GDBController(gdb_path=GDB_PATH, gdb_port=GDB_PORT, elf_file=elf_path)

                # Provide the marker name and extract the start and end address from the dis file
                function_name = "PENTEST_MARKER_P256_VERIFY"
                # Gives back an array of hits where the function is called
                trace_address = parser.get_marker_addresses(function_name)
                print("Start and stop addresses of ", function_name, ": ", trace_address)

                crash_observation_address = parser.get_function_start_address(
                    "ottf_exception_handler"
                )

                # Start the tracing
                # We set a short timeout to detect whether GDB has connected properly
                # and a long timeout for the entire tracing
                initial_timeout = 10
                total_timeout = 60 * 60 * 5

                gdb.setup_pc_trace(pc_trace_file, trace_address[0], trace_address[1])
                gdb.send_command("c", check_response=False)

                # Trigger the p256 verify from the testOS (we do not read its output)
                asymfi.handle_p256_verify(
                    pubx, puby, r_bytes, s_bytes, message_digest, cfg, trigger
                )

                start_time = time.time()
                initial_timeout_stopped = False
                total_timeout_stopped = False

                # Run the tracing to get the trace log
                while time.time() - start_time < initial_timeout:
                    output = gdb.read_output()
                    if "breakpoint 1, " in output:
                        initial_timeout_stopped = True
                        break
                if not initial_timeout_stopped:
                    print("No initial break point found, can be a misfire, try again")
                    sys.exit(1)
                while time.time() - start_time < total_timeout:
                    output = gdb.read_output()
                    if "PC trace complete" in output:
                        print("\nTrace complete")
                        total_timeout_stopped = True
                        break
                if not total_timeout_stopped:
                    print("Final tracing timeout reached")
                    sys.exit(1)

                # Parse and truncate the trace log to get all PCs in a list
                pc_list = gdb.parse_pc_trace_file(pc_trace_file)
                # Get the unique PCs and annotate their occurence count
                pc_count_dict = Counter(pc_list)
                if len(pc_count_dict) <= 0:
                    print("Found no tracing, stopping")
                    sys.exit(1)
                print("Tracing has a total of", len(pc_count_dict), "unique PCs", flush=True)

                # Reset the target, flush the output, and close gdb
                gdb = reset_target_and_gdb(gdb)

                started = True
                for pc, count in pc_count_dict.items():
                    for i_count in range(min(MAX_SKIPS_PER_LOOP, count)):
                        print("-" * 80)
                        print("Applying instruction skip in ", pc, "occurence", i_count)
                        print("-" * 80)

                        crash_observation = "crash detected"

                        try:
                            # The observation points
                            observations = {
                                # Crash check
                                crash_observation_address: f"{crash_observation}",
                            }
                            gdb.add_observation(observations)

                            gdb.apply_instruction_skip(
                                pc, parser.parse_next_instruction(pc), i_count
                            )
                            gdb.send_command("c", check_response=False)

                            # The instruction skip loop
                            asymfi.handle_p256_verify(
                                pubx, puby, r_bytes, s_bytes, message_digest, cfg, trigger
                            )
                            testos_response = read_testos_output()

                            gdb_response = gdb.read_output()
                            if "instruction skip applied" in gdb_response:
                                total_attacks += 1

                                if crash_observation in gdb_response:
                                    print("Crash detected, resetting", flush=True)
                                    gdb = reset_target_and_gdb(gdb)
                                else:
                                    testos_response_json = json.loads(testos_response)
                                    print("Output:", testos_response_json, flush=True)
                                    verification_result = testos_response_json["result"]
                                    verification_status = testos_response_json["status"]
                                    if verification_result and (verification_status == 0):
                                        successful_faults += 1
                                        print("-" * 80)
                                        print("Successful FI attack!")
                                        print("Location:", pc, "iteration", i_count)
                                        print(gdb_response)
                                        print("Response:", testos_response_json)
                                        print("-" * 80)
                                        test_results.write(
                                            f"{pc}, {i_count}: {testos_response_json}\n"
                                        )
                                    # Reset GDB by closing and opening again
                                    gdb = reset_gdb(gdb)
                                    # We do not need to reset the target since it gave an output
                            else:
                                print("No break point found, something went wrong", flush=True)
                                gdb = re_initialize(gdb)

                        except json.JSONDecodeError:
                            print(
                                "Error: JSON decoding failed. Invalid response format",
                                flush=True,
                            )
                            try:
                                gdb = reset_target_and_gdb(gdb)
                            except TimeoutError:
                                gdb = re_initialize(gdb)

                        except TimeoutError as e:
                            print("Timeout error, retrying", flush=True)
                            print(e, flush=True)
                            try:
                                gdb = reset_target_and_gdb(gdb)
                            except TimeoutError:
                                gdb = re_initialize(gdb)

            finally:
                print("-" * 80)
                print("Trace data is logged in ", pc_trace_file)
                print("The campaign is logged in ", campaign_file)
                print("Instruction skip results are logged in ", test_results_file)
                print(f"Total attacks {total_attacks}, successful attacks {successful_faults}")
                print("You can find the dissassembly in ", dis_path)
                # Close the OpenOCD and GDB connection at the end
                if gdb:
                    gdb.close_gdb()
                target.close_openocd()
                test_results.write(
                    f"Total attacks {total_attacks}, successful attacks {successful_faults}\n"
                )
                sys.stdout = original_stdout
                print("Trace data is logged in ", pc_trace_file)
                print("The campaign is logged in ", campaign_file)
                print("Instruction skip results are logged in ", test_results_file)
                print(f"Total attacks {total_attacks}, successful attacks {successful_faults}")
                print("You can find the dissassembly in ", dis_path)
                self.assertEqual(successful_faults, 0)
                self.assertEqual(started, True)

    def test_p256_ecdh(self):
        print("Starting the p256 ecdh test")
        # Preparing the input for an invalid signature
        private_key1 = ECC.generate(curve="P-256")
        private_key_array1 = [x for x in private_key1.d.to_bytes(32, "little")]
        private_key2 = ECC.generate(curve="P-256")
        private_key_array2 = [x for x in private_key2.d.to_bytes(32, "little")]
        private_key_array = [private_key_array1, private_key_array2]
        key = ECC.generate(curve="P-256")
        public_point = key.pointQ
        public_x = [x for x in public_point.x.to_bytes(32, "little")]
        public_y = [x for x in public_point.y.to_bytes(32, "little")]
        cfg = 0
        trigger = 0

        # Directory for the trace log files
        pc_trace_file = os.path.join(log_dir, "p256_ecdh_pc_trace.log")
        # Directory for the output results
        test_results_file = os.path.join(log_dir, "p256_ecdh_test_results.log")
        # Directory for the the log of the campaign
        campaign_file = os.path.join(log_dir, "p256_ecdh_test_campaign.log")

        successful_faults = 0
        total_attacks = 0

        def trigger_testos_init(print_output=True):
            # Initializing the testOS (setting up the alerts and accelerators)
            (device_id, _, _, _, _, _, _) = asymfi.init(
                alert_config=common_library.no_escalation_alert_config
            )
            if print_output:
                print("Output from init ", device_id)

        def read_testos_output():
            # Read the output from the operation
            response = target.read_response(max_tries=1000)
            return response

        def reset_gdb(gdb):
            gdb.close_gdb()
            gdb = GDBController(
                gdb_path=GDB_PATH,
                gdb_port=GDB_PORT,
                elf_file=elf_path,
            )
            return gdb

        def reset_target_and_gdb(gdb):
            gdb.close_gdb()
            gdb = GDBController(
                gdb_path=GDB_PATH,
                gdb_port=GDB_PORT,
                elf_file=elf_path,
            )
            gdb.reset_target()
            target.dump_all()
            trigger_testos_init(print_output=False)
            # Reset again
            gdb.close_gdb()
            gdb = GDBController(
                gdb_path=GDB_PATH,
                gdb_port=GDB_PORT,
                elf_file=elf_path,
            )
            gdb.dump_output()
            target.dump_all()
            return gdb

        def re_initialize(gdb):
            gdb.close_gdb()
            target.close_openocd()
            target.initialize_target()
            trigger_testos_init()
            target.dump_all()
            gdb = GDBController(gdb_path=GDB_PATH, gdb_port=GDB_PORT, elf_file=elf_path)
            return gdb

        ecdh_output = [None, None]

        gdb = None
        started = False
        with open(test_results_file, "w") as test_results, open(campaign_file, "w") as campaign:
            print(f"Switching terminal output to {campaign_file}", flush=True)
            sys.stdout = campaign
            try:
                # Program the bitstream, flash the target, and set up OpenOCD
                target.initialize_target()

                # Initialize the testOS
                trigger_testos_init()

                # Connect to GDB
                gdb = GDBController(gdb_path=GDB_PATH, gdb_port=GDB_PORT, elf_file=elf_path)

                # We provide the name of the unique marker in the pentest framework
                function_name = "PENTEST_MARKER_P256_ECDH"
                # Gives back an array of hits where the function is called
                trace_address = parser.get_marker_addresses(function_name)
                print("Start and stop addresses of ", function_name, ": ", trace_address)

                crash_observation_address = parser.get_function_start_address(
                    "ottf_exception_handler"
                )

                # Start the tracing
                # We set a short timeout to detect whether GDB has connected properly
                # and a long timeout for the entire tracing
                initial_timeout = 10
                total_timeout = 60 * 60 * 5

                gdb.setup_pc_trace(pc_trace_file, trace_address[0], trace_address[1])
                gdb.send_command("c", check_response=False)

                # Trigger the p256 verify from the testOS (we do not read its output)
                asymfi.handle_p256_ecdh(private_key_array[0], public_x, public_y, cfg, trigger)

                start_time = time.time()
                initial_timeout_stopped = False
                total_timeout_stopped = False

                # Run the tracing to get the trace log
                while time.time() - start_time < initial_timeout:
                    output = gdb.read_output()
                    if "breakpoint 1, " in output:
                        initial_timeout_stopped = True
                        break
                if not initial_timeout_stopped:
                    print("No initial break point found, can be a misfire, try again")
                    sys.exit(1)
                while time.time() - start_time < total_timeout:
                    output = gdb.read_output()
                    if "PC trace complete" in output:
                        print("\nTrace complete")
                        total_timeout_stopped = True
                        break
                if not total_timeout_stopped:
                    print("Final tracing timeout reached")
                    sys.exit(1)

                # Parse and truncate the trace log to get all PCs in a list
                pc_list = gdb.parse_pc_trace_file(pc_trace_file)
                # Get the unique PCs and annotate their occurence count
                pc_count_dict = Counter(pc_list)
                if len(pc_count_dict) <= 0:
                    print("Found no tracing, stopping")
                    sys.exit(1)
                print("Tracing has a total of", len(pc_count_dict), "unique PCs", flush=True)

                # Reset the target, flush the output, and close gdb
                gdb = re_initialize(gdb)

                started = True
                for pc, count in pc_count_dict.items():
                    for i_count in range(min(MAX_SKIPS_PER_LOOP, count)):
                        # Search for collisions in outputs between the ecdh instances
                        for i in range(2):
                            print("-" * 80)
                            print("Applying instruction skip in ", pc, "occurence", i_count)
                            print("-" * 80)

                            crash_observation = "crash detected"

                            try:
                                # The observation points
                                observations = {
                                    # Crash check
                                    crash_observation_address: f"{crash_observation}",
                                }
                                gdb.add_observation(observations)

                                gdb.apply_instruction_skip(
                                    pc, parser.parse_next_instruction(pc), i_count
                                )
                                gdb.send_command("c", check_response=False)

                                # The instruction skip loop
                                asymfi.handle_p256_ecdh(
                                    private_key_array[i], public_x, public_y, cfg, trigger
                                )
                                testos_response = read_testos_output()

                                gdb_response = gdb.read_output()
                                if "instruction skip applied" in gdb_response:
                                    total_attacks += 1

                                    if crash_observation in gdb_response:
                                        print("Crash detected, resetting", flush=True)
                                        gdb = reset_target_and_gdb(gdb)
                                    else:
                                        testos_response_json = json.loads(testos_response)
                                        print("Output:", testos_response_json, flush=True)
                                        if testos_response_json["status"] == 0:
                                            ecdh_output[i] = testos_response_json["shared_key"]
                                            if ecdh_output[i] == ecdh_output[1 - i]:
                                                successful_faults += 1
                                                print("-" * 80)
                                                print("Successful FI attack!")
                                                print("Location:", pc, "iteration", i_count)
                                                print(gdb_response)
                                                print("Response:", testos_response_json)
                                                print("-" * 80)
                                                test_results.write(
                                                    f"{pc}, {i_count}: {testos_response_json}\n"
                                                )
                                        # Reset GDB by closing and opening again
                                        gdb = reset_gdb(gdb)
                                        # We do not need to reset the target since it gave an output
                                else:
                                    print("No break point found, something went wrong", flush=True)
                                    gdb = re_initialize(gdb)

                            except json.JSONDecodeError:
                                print(
                                    "Error: JSON decoding failed. Invalid response format",
                                    flush=True,
                                )
                                try:
                                    gdb = reset_target_and_gdb(gdb)
                                except TimeoutError:
                                    gdb = re_initialize(gdb)

                            except TimeoutError as e:
                                print("Timeout error, retrying", flush=True)
                                print(e, flush=True)
                                try:
                                    gdb = reset_target_and_gdb(gdb)
                                except TimeoutError:
                                    gdb = re_initialize(gdb)

            finally:
                print("-" * 80)
                print("Trace data is logged in ", pc_trace_file)
                print("The campaign is logged in ", campaign_file)
                print("Instruction skip results are logged in ", test_results_file)
                print(f"Total attacks {total_attacks}, successful attacks {successful_faults}")
                print("You can find the dissassembly in ", dis_path)
                # Close the OpenOCD and GDB connection at the end
                if gdb:
                    gdb.close_gdb()
                target.close_openocd()
                test_results.write(
                    f"Total attacks {total_attacks}, successful attacks {successful_faults}\n"
                )
                sys.stdout = original_stdout
                print("Trace data is logged in ", pc_trace_file)
                print("The campaign is logged in ", campaign_file)
                print("Instruction skip results are logged in ", test_results_file)
                print(f"Total attacks {total_attacks}, successful attacks {successful_faults}")
                print("You can find the dissassembly in ", dis_path)
                self.assertEqual(successful_faults, 0)
                self.assertEqual(started, True)

    def test_rsa_pkcs1v15_verify(self):
        print("Starting the rsa pkcs1v15 verify test")
        # Preparing the input for an invalid signature
        key = RSA.generate(2048)
        public_exponent = key.e
        n = [x for x in (key.n).to_bytes(256, "little")]
        n_len = 256
        data_len = 13
        data = [i for i in range(data_len)]
        h = SHA256.new(bytes(data))
        signer = pkcs1_15.new(key)
        signature = signer.sign(h)
        sig = [x for x in signature]
        # Corrupt the signature for FiSim Testing
        sig[0] ^= 0x1
        sig.reverse()
        sig_len = len(sig)
        cfg = 0
        trigger = 0x4
        hashing = 0
        # pkcs1v15
        padding = 0

        # Directory for the trace log files
        pc_trace_file = os.path.join(log_dir, "rsa_verify_pkcs1v15_pc_trace.log")
        # Directory for the output results
        test_results_file = os.path.join(log_dir, "rsa_verify_pkcs1v15_test_results.log")
        # Directory for the the log of the campaign
        campaign_file = os.path.join(log_dir, "rsa_verify_pkcs1v15_test_campaign.log")

        successful_faults = 0
        total_attacks = 0

        def trigger_testos_init(print_output=True):
            # Initializing the testOS (setting up the alerts and accelerators)
            (device_id, _, _, _, _, _, _) = asymfi.init(
                alert_config=common_library.no_escalation_alert_config
            )
            if print_output:
                print("Output from init ", device_id)

        def read_testos_output():
            # Read the output from the operation
            response = target.read_response(max_tries=1000)
            return response

        def reset_gdb(gdb):
            gdb.close_gdb()
            gdb = GDBController(
                gdb_path=GDB_PATH,
                gdb_port=GDB_PORT,
                elf_file=elf_path,
            )
            return gdb

        def reset_target_and_gdb(gdb):
            gdb.close_gdb()
            gdb = GDBController(
                gdb_path=GDB_PATH,
                gdb_port=GDB_PORT,
                elf_file=elf_path,
            )
            gdb.reset_target()
            target.dump_all()
            trigger_testos_init(print_output=False)
            # Reset again
            gdb.close_gdb()
            gdb = GDBController(
                gdb_path=GDB_PATH,
                gdb_port=GDB_PORT,
                elf_file=elf_path,
            )
            gdb.dump_output()
            target.dump_all()
            return gdb

        def re_initialize(gdb):
            gdb.close_gdb()
            target.close_openocd()
            target.initialize_target()
            trigger_testos_init()
            target.dump_all()
            gdb = GDBController(gdb_path=GDB_PATH, gdb_port=GDB_PORT, elf_file=elf_path)
            return gdb

        gdb = None
        started = False
        with open(test_results_file, "w") as test_results, open(campaign_file, "w") as campaign:
            print(f"Switching terminal output to {campaign_file}", flush=True)
            sys.stdout = campaign
            try:
                # Program the bitstream, flash the target, and set up OpenOCD
                target.initialize_target()

                # Initialize the testOS
                trigger_testos_init()

                # Connect to GDB
                gdb = GDBController(gdb_path=GDB_PATH, gdb_port=GDB_PORT, elf_file=elf_path)

                # Provide the marker name and extract the start and end address from the dis file
                function_name = "PENTEST_MARKER_RSA_VERIFY"
                # Gives back an array of hits where the function is called
                trace_address = parser.get_marker_addresses(function_name)
                print("Start and stop addresses of ", function_name, ": ", trace_address)

                crash_observation_address = parser.get_function_start_address(
                    "ottf_exception_handler"
                )

                # Start the tracing
                # We set a short timeout to detect whether GDB has connected properly
                # and a long timeout for the entire tracing
                initial_timeout = 10
                total_timeout = 60 * 60 * 5

                gdb.setup_pc_trace(pc_trace_file, trace_address[0], trace_address[1])
                gdb.send_command("c", check_response=False)

                # Trigger the rsa verify from the testOS (we do not read its output)
                asymfi.handle_rsa_verify(
                    data,
                    data_len,
                    public_exponent,
                    n,
                    n_len,
                    sig,
                    sig_len,
                    padding,
                    hashing,
                    cfg,
                    trigger,
                )

                start_time = time.time()
                initial_timeout_stopped = False
                total_timeout_stopped = False

                # Run the tracing to get the trace log
                # Sometimes the tracing fails due to race conditions,
                # we have a quick initial timeout to catch this
                while time.time() - start_time < initial_timeout:
                    output = gdb.read_output()
                    if "breakpoint 1, " in output:
                        initial_timeout_stopped = True
                        break
                if not initial_timeout_stopped:
                    print("No initial break point found, can be a misfire, try again")
                    sys.exit(1)
                while time.time() - start_time < total_timeout:
                    output = gdb.read_output()
                    if "PC trace complete" in output:
                        print("\nTrace complete")
                        total_timeout_stopped = True
                        break
                if not total_timeout_stopped:
                    print("Final tracing timeout reached")
                    sys.exit(1)

                # Parse and truncate the trace log to get all PCs in a list
                pc_list = gdb.parse_pc_trace_file(pc_trace_file)
                # Get the unique PCs and annotate their occurence count
                pc_count_dict = Counter(pc_list)
                if len(pc_count_dict) <= 0:
                    print("Found no tracing, stopping")
                    sys.exit(1)
                print("Tracing has a total of", len(pc_count_dict), "unique PCs", flush=True)

                # Reset the target, flush the output, and close gdb
                gdb = re_initialize(gdb)

                started = True
                for pc, count in pc_count_dict.items():
                    for i_count in range(min(MAX_SKIPS_PER_LOOP, count)):
                        print("-" * 80)
                        print("Applying instruction skip in ", pc, "occurence", i_count)
                        print("-" * 80)

                        crash_observation = "crash detected"

                        try:
                            # The observation points
                            observations = {
                                # Crash check
                                crash_observation_address: f"{crash_observation}",
                            }
                            gdb.add_observation(observations)

                            gdb.apply_instruction_skip(
                                pc, parser.parse_next_instruction(pc), i_count
                            )
                            gdb.send_command("c", check_response=False)

                            # The instruction skip loop
                            asymfi.handle_rsa_verify(
                                data,
                                data_len,
                                public_exponent,
                                n,
                                n_len,
                                sig,
                                sig_len,
                                padding,
                                hashing,
                                cfg,
                                trigger,
                            )
                            testos_response = read_testos_output()

                            gdb_response = gdb.read_output()
                            if "instruction skip applied" in gdb_response:
                                total_attacks += 1

                                if crash_observation in gdb_response:
                                    print("Crash detected, resetting", flush=True)
                                    gdb = reset_target_and_gdb(gdb)
                                else:
                                    testos_response_json = json.loads(testos_response)
                                    print("Output:", testos_response_json, flush=True)
                                    verification_result = testos_response_json["result"]
                                    verification_status = testos_response_json["status"]
                                    if verification_result and (verification_status == 0):
                                        successful_faults += 1
                                        print("-" * 80)
                                        print("Successful FI attack!")
                                        print("Location:", pc, "iteration", i_count)
                                        print(gdb_response)
                                        print("Response:", testos_response_json)
                                        print("-" * 80)
                                        test_results.write(
                                            f"{pc}, {i_count}: {testos_response_json}\n"
                                        )
                                    # Reset GDB by closing and opening again
                                    gdb = reset_gdb(gdb)
                                    # We do not need to reset the target since it returned an output
                            else:
                                print("No break point found, something went wrong", flush=True)
                                gdb = re_initialize(gdb)

                        except json.JSONDecodeError:
                            print(
                                "Error: JSON decoding failed. Invalid response format",
                                flush=True,
                            )
                            try:
                                gdb = reset_target_and_gdb(gdb)
                            except TimeoutError:
                                gdb = re_initialize(gdb)

                        except TimeoutError as e:
                            print("Timeout error, retrying", flush=True)
                            print(e, flush=True)
                            try:
                                gdb = reset_target_and_gdb(gdb)
                            except TimeoutError:
                                gdb = re_initialize(gdb)

            finally:
                print("-" * 80)
                print("Trace data is logged in ", pc_trace_file)
                print("The campaign is logged in ", campaign_file)
                print("Instruction skip results are logged in ", test_results_file)
                print(f"Total attacks {total_attacks}, successful attacks {successful_faults}")
                print("You can find the dissassembly in ", dis_path)
                # Close the OpenOCD and GDB connection at the end
                if gdb:
                    gdb.close_gdb()
                target.close_openocd()
                test_results.write(
                    f"Total attacks {total_attacks}, successful attacks {successful_faults}\n"
                )
                sys.stdout = original_stdout
                print("Trace data is logged in ", pc_trace_file)
                print("The campaign is logged in ", campaign_file)
                print("Instruction skip results are logged in ", test_results_file)
                print(f"Total attacks {total_attacks}, successful attacks {successful_faults}")
                print("You can find the dissassembly in ", dis_path)
                self.assertEqual(successful_faults, 0)
                self.assertEqual(started, True)

    def test_rsa_pss_verify(self):
        print("Starting the rsa pss verify test")
        # Preparing the input for an invalid signature
        key = RSA.generate(2048)
        public_exponent = key.e
        n = [x for x in (key.n).to_bytes(256, "little")]
        n_len = 256
        data_len = 13
        data = [i for i in range(data_len)]
        h = SHA256.new(bytes(data))
        signer = pkcs1_15.new(key)
        signature = signer.sign(h)
        sig = [x for x in signature]
        # Corrupt the signature for FiSim Testing
        sig[0] ^= 0x1
        sig.reverse()
        sig_len = len(sig)
        cfg = 0
        trigger = 0x4
        hashing = 0
        # pss
        padding = 1

        # Directory for the trace log files
        pc_trace_file = os.path.join(log_dir, "rsa_verify_pss_pc_trace.log")
        # Directory for the output results
        test_results_file = os.path.join(log_dir, "rsa_verify_pss_test_results.log")
        # Directory for the the log of the campaign
        campaign_file = os.path.join(log_dir, "rsa_verify_pss_test_campaign.log")

        successful_faults = 0
        total_attacks = 0

        def trigger_testos_init(print_output=True):
            # Initializing the testOS (setting up the alerts and accelerators)
            (device_id, _, _, _, _, _, _) = asymfi.init(
                alert_config=common_library.no_escalation_alert_config
            )
            if print_output:
                print("Output from init ", device_id)

        def read_testos_output():
            # Read the output from the operation
            response = target.read_response(max_tries=1000)
            return response

        def reset_gdb(gdb):
            gdb.close_gdb()
            gdb = GDBController(
                gdb_path=GDB_PATH,
                gdb_port=GDB_PORT,
                elf_file=elf_path,
            )
            return gdb

        def reset_target_and_gdb(gdb):
            gdb.close_gdb()
            gdb = GDBController(
                gdb_path=GDB_PATH,
                gdb_port=GDB_PORT,
                elf_file=elf_path,
            )
            gdb.reset_target()
            target.dump_all()
            trigger_testos_init(print_output=False)
            # Reset again
            gdb.close_gdb()
            gdb = GDBController(
                gdb_path=GDB_PATH,
                gdb_port=GDB_PORT,
                elf_file=elf_path,
            )
            gdb.dump_output()
            target.dump_all()
            return gdb

        def re_initialize(gdb):
            gdb.close_gdb()
            target.close_openocd()
            target.initialize_target()
            trigger_testos_init()
            target.dump_all()
            gdb = GDBController(gdb_path=GDB_PATH, gdb_port=GDB_PORT, elf_file=elf_path)
            return gdb

        gdb = None
        started = False
        with open(test_results_file, "w") as test_results, open(campaign_file, "w") as campaign:
            print(f"Switching terminal output to {campaign_file}", flush=True)
            sys.stdout = campaign
            try:
                # Program the bitstream, flash the target, and set up OpenOCD
                target.initialize_target()

                # Initialize the testOS
                trigger_testos_init()

                # Connect to GDB
                gdb = GDBController(gdb_path=GDB_PATH, gdb_port=GDB_PORT, elf_file=elf_path)

                # Provide the marker name and extract the start and end address from the dis file
                function_name = "PENTEST_MARKER_RSA_VERIFY"
                # Gives back an array of hits where the function is called
                trace_address = parser.get_marker_addresses(function_name)
                print("Start and stop addresses of ", function_name, ": ", trace_address)

                crash_observation_address = parser.get_function_start_address(
                    "ottf_exception_handler"
                )

                # Start the tracing
                # We set a short timeout to detect whether GDB has connected properly
                # and a long timeout for the entire tracing
                initial_timeout = 10
                total_timeout = 60 * 60 * 5

                gdb.setup_pc_trace(pc_trace_file, trace_address[0], trace_address[1])
                gdb.send_command("c", check_response=False)

                # Trigger the rsa verify from the testOS (we do not read its output)
                asymfi.handle_rsa_verify(
                    data,
                    data_len,
                    public_exponent,
                    n,
                    n_len,
                    sig,
                    sig_len,
                    padding,
                    hashing,
                    cfg,
                    trigger,
                )

                start_time = time.time()
                initial_timeout_stopped = False
                total_timeout_stopped = False

                # Run the tracing to get the trace log
                # Sometimes the tracing fails due to race conditions,
                # we have a quick initial timeout to catch this
                while time.time() - start_time < initial_timeout:
                    output = gdb.read_output()
                    if "breakpoint 1, " in output:
                        initial_timeout_stopped = True
                        break
                if not initial_timeout_stopped:
                    print("No initial break point found, can be a misfire, try again")
                    sys.exit(1)
                while time.time() - start_time < total_timeout:
                    output = gdb.read_output()
                    if "PC trace complete" in output:
                        print("\nTrace complete")
                        total_timeout_stopped = True
                        break
                if not total_timeout_stopped:
                    print("Final tracing timeout reached")
                    sys.exit(1)

                # Parse and truncate the trace log to get all PCs in a list
                pc_list = gdb.parse_pc_trace_file(pc_trace_file)
                # Get the unique PCs and annotate their occurence count
                pc_count_dict = Counter(pc_list)
                if len(pc_count_dict) <= 0:
                    print("Found no tracing, stopping")
                    sys.exit(1)
                print("Tracing has a total of", len(pc_count_dict), "unique PCs", flush=True)

                # Reset the target, flush the output, and close gdb
                gdb = re_initialize(gdb)

                started = True
                for pc, count in pc_count_dict.items():
                    for i_count in range(min(MAX_SKIPS_PER_LOOP, count)):
                        print("-" * 80)
                        print("Applying instruction skip in ", pc, "occurence", i_count)
                        print("-" * 80)

                        crash_observation = "crash detected"

                        try:
                            # The observation points
                            observations = {
                                # Crash check
                                crash_observation_address: f"{crash_observation}",
                            }
                            gdb.add_observation(observations)

                            gdb.apply_instruction_skip(
                                pc, parser.parse_next_instruction(pc), i_count
                            )
                            gdb.send_command("c", check_response=False)

                            # The instruction skip loop
                            asymfi.handle_rsa_verify(
                                data,
                                data_len,
                                public_exponent,
                                n,
                                n_len,
                                sig,
                                sig_len,
                                padding,
                                hashing,
                                cfg,
                                trigger,
                            )
                            testos_response = read_testos_output()

                            gdb_response = gdb.read_output()
                            if "instruction skip applied" in gdb_response:
                                total_attacks += 1

                                if crash_observation in gdb_response:
                                    print("Crash detected, resetting", flush=True)
                                    gdb = reset_target_and_gdb(gdb)
                                else:
                                    testos_response_json = json.loads(testos_response)
                                    print("Output:", testos_response_json, flush=True)
                                    verification_result = testos_response_json["result"]
                                    verification_status = testos_response_json["status"]
                                    if verification_result and (verification_status == 0):
                                        successful_faults += 1
                                        print("-" * 80)
                                        print("Successful FI attack!")
                                        print("Location:", pc, "iteration", i_count)
                                        print(gdb_response)
                                        print("Response:", testos_response_json)
                                        print("-" * 80)
                                        test_results.write(
                                            f"{pc}, {i_count}: {testos_response_json}\n"
                                        )
                                    # Reset GDB by closing and opening again
                                    gdb = reset_gdb(gdb)
                                    # We do not need to reset the target since it returned an output
                            else:
                                print("No break point found, something went wrong", flush=True)
                                gdb = re_initialize(gdb)

                        except json.JSONDecodeError:
                            print(
                                "Error: JSON decoding failed. Invalid response format",
                                flush=True,
                            )
                            try:
                                gdb = reset_target_and_gdb(gdb)
                            except TimeoutError:
                                gdb = re_initialize(gdb)

                        except TimeoutError as e:
                            print("Timeout error, retrying", flush=True)
                            print(e, flush=True)
                            try:
                                gdb = reset_target_and_gdb(gdb)
                            except TimeoutError:
                                gdb = re_initialize(gdb)

            finally:
                print("-" * 80)
                print("Trace data is logged in ", pc_trace_file)
                print("The campaign is logged in ", campaign_file)
                print("Instruction skip results are logged in ", test_results_file)
                print(f"Total attacks {total_attacks}, successful attacks {successful_faults}")
                print("You can find the dissassembly in ", dis_path)
                # Close the OpenOCD and GDB connection at the end
                if gdb:
                    gdb.close_gdb()
                target.close_openocd()
                test_results.write(
                    f"Total attacks {total_attacks}, successful attacks {successful_faults}\n"
                )
                sys.stdout = original_stdout
                print("Trace data is logged in ", pc_trace_file)
                print("The campaign is logged in ", campaign_file)
                print("Instruction skip results are logged in ", test_results_file)
                print(f"Total attacks {total_attacks}, successful attacks {successful_faults}")
                print("You can find the dissassembly in ", dis_path)
                self.assertEqual(successful_faults, 0)
                self.assertEqual(started, True)


if __name__ == "__main__":
    r = Runfiles.Create()
    # Get the openocd path.
    openocd_path = r.Rlocation("lowrisc_opentitan/third_party/openocd/build_openocd/bin/openocd")
    # Get the openocd config files.
    # The first file is on the cw340 (this is specific to the cw340)
    CONFIG_FILE_CHIP = r.Rlocation("lowrisc_opentitan/util/openocd/board/cw340_ftdi.cfg")
    # The config for the earlgrey design
    CONFIG_FILE_DESIGN = r.Rlocation("lowrisc_opentitan/util/openocd/target/lowrisc-earlgrey.cfg")
    # Get the opentitantool path.
    opentitantool_path = r.Rlocation("lowrisc_opentitan/sw/host/opentitantool/opentitantool")
    # The path for GDB and the default port (set up by OpenOCD)
    GDB_PATH = r.Rlocation("lowrisc_rv32imcb_toolchain/bin/riscv32-unknown-elf-gdb")
    GDB_PORT = 3333
    # Program the bitstream for FPGAs.
    bitstream_path = None
    if BITSTREAM:
        bitstream_path = r.Rlocation("lowrisc_opentitan/" + BITSTREAM)
    # Get the test result path
    log_dir = os.environ.get("TEST_UNDECLARED_OUTPUTS_DIR")
    # Get the firmware path.
    firmware_path = r.Rlocation("lowrisc_opentitan/" + BOOTSTRAP)
    # Get the disassembly path.
    dis_path = firmware_path.replace(".img", ".dis")
    # And the path for the elf.
    elf_path = firmware_path.replace(".img", ".elf")

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
        openocd=openocd_path,
        openocd_chip_config=CONFIG_FILE_CHIP,
        openocd_design_config=CONFIG_FILE_DESIGN,
    )

    target = targets.Target(target_cfg)
    asymfi = OTFIAsymCrypto(target)
    parser = DisParser(dis_path)

    print("Disassembly is found in ", dis_path, flush=True)

    unittest.main(argv=[sys.argv[0]])
