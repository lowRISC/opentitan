# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# What to do when running into errors:
# - If device is busy or seeing "rejected 'gdb' connection, no more connections allowed",
# cut the USB connection, e.g., sudo fuser /dev/ttyUSB0 and kill the PID
# - If the port is busy check sudo lsof -i :3333 and then kill the PID

from sw.host.penetrationtests.python.fi.communication.fi_sym_cryptolib_commands import (
    OTFISymCrypto,
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

ignored_keys_set = set(["status"])
opentitantool_path = ""
log_dir = ""
elf_path = ""

# We set to only apply instruction skips in the first
# MAX_SKIPS_PER_LOOP iterations of a loop
MAX_SKIPS_PER_LOOP = 2

target = None
symfi = None

# Read in the extra arguments from the opentitan_test.
parser = argparse.ArgumentParser()
parser.add_argument("--bitstream", type=str)
parser.add_argument("--bootstrap", type=str)

args, config_args = parser.parse_known_args()

BITSTREAM = args.bitstream
BOOTSTRAP = args.bootstrap

original_stdout = sys.stdout


def trigger_testos_init(print_output=True):
    # Initializing the testOS (setting up the alerts and accelerators)
    (device_id, _, _, _, _, _, _) = symfi.init(
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
    target.reset_target()
    target.start_openocd(startup_delay=0.2, print_output=False)
    target.dump_all()
    trigger_testos_init(print_output=False)
    gdb = GDBController(
        gdb_path=GDB_PATH,
        gdb_port=GDB_PORT,
        elf_file=elf_path,
    )
    return gdb


def re_initialize(gdb, print_output=False):
    gdb.close_gdb()
    target.initialize_target(print_output=print_output)
    trigger_testos_init(print_output=print_output)
    target.dump_all()
    gdb = GDBController(gdb_path=GDB_PATH, gdb_port=GDB_PORT, elf_file=elf_path)
    return gdb


class SymCryptolibFiSim(unittest.TestCase):
    def test_hmac(self):
        print("Starting the hmac-sha256 test")
        # We only test SHA256
        data_len = 32
        # We prepare two data inputs and check for collisions between them
        data1 = [i for i in range(data_len)]
        data2 = [data_len - i for i in range(data_len)]
        data = [data1, data2]
        key_len = 32
        key = [i for i in range(key_len)]
        cfg = 0
        trigger = 0
        hash_mode = 0
        mode = 0

        # Directory for the trace log files
        pc_trace_file = os.path.join(log_dir, "hmac_pc_trace.log")
        # Directory for the the log of the campaign
        campaign_file = os.path.join(log_dir, "hmac_test_campaign.log")

        successful_faults = 0
        total_attacks = 0

        gdb = None
        started = False
        with open(campaign_file, "w") as campaign:
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
                function_name = "PENTEST_MARKER_HMAC"
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

                # Trigger the hmac from the testOS (we do not read its output)
                symfi.handle_hmac(data[0], data_len, key, key_len, hash_mode, mode, cfg, trigger)

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
                print("Trace data is logged in ", pc_trace_file)
                print("Tracing has a total of", len(pc_count_dict), "unique PCs", flush=True)

                # Reset the target, flush the output, and close gdb
                gdb = reset_target_and_gdb(gdb)

                data_out = [None, None]

                started = True
                for pc, count in pc_count_dict.items():
                    for i_count in range(min(MAX_SKIPS_PER_LOOP, count)):
                        # Search for collisions in outputs between the hmac instances
                        for i in range(2):
                            print("-" * 80)
                            print(
                                "Applying instruction skip in ", pc, "occurence", i_count, "data", i
                            )
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
                                symfi.handle_hmac(
                                    data[i], data_len, key, key_len, hash_mode, mode, cfg, trigger
                                )
                                testos_response = read_testos_output()

                                gdb_response = gdb.read_output()
                                data_out[i] = None
                                if "instruction skip applied" in gdb_response:
                                    i_count += 1
                                    total_attacks += 1

                                    if crash_observation in gdb_response:
                                        print("Crash detected, resetting", flush=True)
                                        gdb = reset_target_and_gdb(gdb)
                                    else:
                                        testos_response_json = json.loads(testos_response)
                                        print("Output:", testos_response_json, flush=True)
                                        if testos_response_json["status"] == 0:
                                            data_out[i] = tuple(testos_response_json["data"])

                                            if data_out[i] == data_out[1 - i]:
                                                successful_faults += 1
                                                print("-" * 80)
                                                print("Successful FI attack!")
                                                print("Location:", pc, "iteration", i_count - 1)
                                                print(gdb_response)
                                                print("Response:", testos_response_json)
                                                print("-" * 80)
                                        # Reset GDB by closing and opening again
                                        gdb = reset_gdb(gdb)
                                else:
                                    print("No break point found, something went wrong", flush=True)
                                    gdb = reset_target_and_gdb(gdb)

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
                print(f"Total attacks {total_attacks}, successful attacks {successful_faults}")
                # Close the OpenOCD and GDB connection at the end
                if gdb:
                    gdb.close_gdb()
                target.close_openocd()
                sys.stdout = original_stdout
                self.assertEqual(successful_faults, 0)
                self.assertEqual(started, True)

    def test_drbg_generate(self):
        print("Starting the drbg generate test")
        entropy_len = 32
        entropy1 = [i for i in range(entropy_len)]
        entropy2 = [entropy_len - i for i in range(entropy_len)]
        entropy = [entropy1, entropy2]
        nonce_len = 16
        nonce = [i for i in range(nonce_len)]
        reseed_interval = 100
        data_len = 16
        mode = 0
        trigger = 2
        cfg = 0

        # Directory for the trace log files
        pc_trace_file = os.path.join(log_dir, "drbg_generate_pc_trace.log")
        # Directory for the the log of the campaign
        campaign_file = os.path.join(log_dir, "drbg_generate_test_campaign.log")

        successful_faults = 0
        total_attacks = 0

        drbg_out = [None, None]

        gdb = None
        started = False
        with open(campaign_file, "w") as campaign:
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
                function_name = "PENTEST_MARKER_DRBG_GENERATE"
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

                # Trigger the drbg from the testOS (we do not read its output)
                symfi.handle_drbg_reseed(
                    entropy[0], entropy_len, nonce, nonce_len, reseed_interval, mode, 0, 0
                )
                target.read_response()
                symfi.handle_drbg_generate([0], 0, data_len, mode, cfg, trigger)

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
                print("Trace data is logged in ", pc_trace_file)
                print("Tracing has a total of", len(pc_count_dict), "unique PCs", flush=True)

                # Reset the target, flush the output, and close gdb
                gdb = reset_target_and_gdb(gdb)

                started = True
                for pc, count in pc_count_dict.items():
                    for i_count in range(min(MAX_SKIPS_PER_LOOP, count)):
                        # Search for collisions in outputs between the drbg instances
                        for i in range(2):
                            print("-" * 80)
                            print(
                                "Applying instruction skip in ", pc, "occurence", i_count, "data", i
                            )
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
                                symfi.handle_drbg_reseed(
                                    entropy[i],
                                    entropy_len,
                                    nonce,
                                    nonce_len,
                                    reseed_interval,
                                    mode,
                                    0,
                                    0,
                                )
                                target.read_response()
                                symfi.handle_drbg_generate([0], 0, data_len, mode, cfg, trigger)
                                testos_response = read_testos_output()

                                gdb_response = gdb.read_output()
                                drbg_out[i] = None
                                if "instruction skip applied" in gdb_response:
                                    i_count += 1
                                    total_attacks += 1

                                    if crash_observation in gdb_response:
                                        print("Crash detected, resetting", flush=True)
                                        gdb = reset_target_and_gdb(gdb)
                                    else:
                                        testos_response_json = json.loads(testos_response)
                                        print("Output:", testos_response_json, flush=True)
                                        if testos_response_json["status"] == 0:
                                            drbg_out[i] = tuple(testos_response_json["data"])

                                            if drbg_out[i] == drbg_out[1 - i]:
                                                successful_faults += 1
                                                print("-" * 80)
                                                print("Successful FI attack!")
                                                print("Location:", pc, "iteration", i_count - 1)
                                                print(gdb_response)
                                                print("Response:", testos_response_json)
                                                print("-" * 80)
                                        # Reset GDB by closing and opening again
                                        gdb = reset_gdb(gdb)
                                else:
                                    print("No break point found, something went wrong", flush=True)
                                    gdb = reset_target_and_gdb(gdb)

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
                print(f"Total attacks {total_attacks}, successful attacks {successful_faults}")
                # Close the OpenOCD and GDB connection at the end
                if gdb:
                    gdb.close_gdb()
                target.close_openocd()
                sys.stdout = original_stdout
                self.assertEqual(successful_faults, 0)
                self.assertEqual(started, True)

    def test_drbg_reseed(self):
        print("Starting the drbg reseed test")
        entropy_len = 32
        entropy1 = [i for i in range(entropy_len)]
        entropy2 = [entropy_len - i for i in range(entropy_len)]
        entropy = [entropy1, entropy2]
        nonce_len = 16
        nonce = [i for i in range(nonce_len)]
        reseed_interval = 100
        data_len = 16
        mode = 0
        trigger = 1
        cfg = 0

        # Directory for the trace log files
        pc_trace_file = os.path.join(log_dir, "drbg_reseed_pc_trace.log")
        # Directory for the the log of the campaign
        campaign_file = os.path.join(log_dir, "drbg_reseed_test_campaign.log")

        successful_faults = 0
        total_attacks = 0

        drbg_out = [None, None]

        gdb = None
        started = False
        with open(campaign_file, "w") as campaign:
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
                function_name = "PENTEST_MARKER_DRBG_RESEED"
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

                # Trigger the drbg from the testOS (we do not read its output)
                symfi.handle_drbg_reseed(
                    entropy[0], entropy_len, nonce, nonce_len, reseed_interval, mode, cfg, trigger
                )
                target.read_response()
                symfi.handle_drbg_generate([0], 0, data_len, mode, cfg, trigger)

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
                print("Trace data is logged in ", pc_trace_file)
                print("Tracing has a total of", len(pc_count_dict), "unique PCs", flush=True)

                # Reset the target, flush the output, and close gdb
                gdb = reset_target_and_gdb(gdb)

                started = True
                for pc, count in pc_count_dict.items():
                    for i_count in range(min(MAX_SKIPS_PER_LOOP, count)):
                        # Search for collisions in outputs between the drbg instances
                        for i in range(2):
                            print("-" * 80)
                            print(
                                "Applying instruction skip in ", pc, "occurence", i_count, "data", i
                            )
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
                                symfi.handle_drbg_reseed(
                                    entropy[i],
                                    entropy_len,
                                    nonce,
                                    nonce_len,
                                    reseed_interval,
                                    mode,
                                    cfg,
                                    trigger,
                                )
                                target.read_response()
                                symfi.handle_drbg_generate([0], 0, data_len, mode, cfg, trigger)
                                testos_response = read_testos_output()

                                gdb_response = gdb.read_output()
                                drbg_out[i] = None
                                if "instruction skip applied" in gdb_response:
                                    total_attacks += 1

                                    if crash_observation in gdb_response:
                                        print("Crash detected, resetting", flush=True)
                                        gdb = reset_target_and_gdb(gdb)
                                    else:
                                        testos_response_json = json.loads(testos_response)
                                        print("Output:", testos_response_json, flush=True)
                                        if testos_response_json["status"] == 0:
                                            drbg_out[i] = testos_response_json["data"]

                                            if drbg_out[i] == drbg_out[1 - i]:
                                                successful_faults += 1
                                                print("-" * 80)
                                                print("Successful FI attack!")
                                                print("Location:", pc, "iteration", i_count)
                                                print(gdb_response)
                                                print("Response:", testos_response_json)
                                                print("-" * 80)
                                        # Reset GDB by closing and opening again
                                        gdb = reset_gdb(gdb)
                                else:
                                    print("No break point found, something went wrong", flush=True)
                                    gdb = reset_target_and_gdb(gdb)

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
                print(f"Total attacks {total_attacks}, successful attacks {successful_faults}")
                # Close the OpenOCD and GDB connection at the end
                if gdb:
                    gdb.close_gdb()
                target.close_openocd()
                sys.stdout = original_stdout
                self.assertEqual(successful_faults, 0)
                self.assertEqual(started, True)

    def test_gcm(self):
        print("Starting the gcm test")
        data_len = 16
        data1 = [i for i in range(data_len)]
        data2 = [data_len - i for i in range(data_len)]
        data = [data1, data2]
        aad_len = 16
        aad = [i for i in range(aad_len)]
        tag_len = 16
        tag = [0 for _ in range(tag_len)]
        key_len = 16
        key = [i for i in range(key_len)]
        iv1 = [i for i in range(16)]
        iv2 = [16 - i for i in range(16)]
        iv = [iv1, iv2]
        cfg = 0
        trigger = 0

        # Directory for the trace log files
        pc_trace_file = os.path.join(log_dir, "gcm_pc_trace.log")
        # Directory for the the log of the campaign
        campaign_file = os.path.join(log_dir, "gcm_test_campaign.log")

        successful_faults = 0
        total_attacks = 0

        gcm_out = [None, None]

        gdb = None
        started = False
        with open(campaign_file, "w") as campaign:
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
                function_name = "PENTEST_MARKER_GCM_ENCRYPT"
                # GCM is fully in SW, thus it is a very long trace.
                # GDB can not fully trace it and it runs to an error in the tracing.
                # To circumvent this, we exclude the investigation of some functions.
                ibex_rnd32_read_address = parser.get_function_start_address("ibex_rnd32_read")
                galois_mul_state_key_address = parser.get_function_start_address(
                    "galois_mul_state_key"
                )
                hardened_memcpy_address = parser.get_function_start_address("hardened_memcpy")
                hardened_memshred_address = parser.get_function_start_address("hardened_memshred")
                hardened_memeq_address = parser.get_function_start_address("hardened_memeq")
                ghash_process_block_address = parser.get_function_start_address(
                    "ghash_process_block"
                )
                ghash_context_integrity_checksum_address = parser.get_function_start_address(
                    "ghash_context_integrity_checksum"
                )
                hmac_key_integrity_checksum_address = parser.get_function_start_address(
                    "hmac_key_integrity_checksum"
                )
                MAX_SKIPS_PER_LOOP_GCM = 1
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

                gdb.setup_pc_trace(
                    pc_trace_file,
                    trace_address[0],
                    trace_address[1],
                    skip_addrs=[
                        ibex_rnd32_read_address,
                        galois_mul_state_key_address,
                        hardened_memcpy_address,
                        hardened_memshred_address,
                        hardened_memeq_address,
                        ghash_process_block_address,
                        ghash_context_integrity_checksum_address,
                        hmac_key_integrity_checksum_address,
                    ],
                )
                gdb.send_command("c", check_response=False)

                # Trigger the gcm from the testOS (we do not read its output)
                symfi.handle_gcm(
                    data[0], data_len, key, key_len, aad, aad_len, tag, tag_len, iv[0], cfg, trigger
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
                print("Trace data is logged in ", pc_trace_file)
                print("Tracing has a total of", len(pc_count_dict), "unique PCs", flush=True)

                # Reset the target, flush the output, and close gdb
                gdb = reset_target_and_gdb(gdb)

                started = True
                for pc, count in pc_count_dict.items():
                    for i_count in range(min(MAX_SKIPS_PER_LOOP_GCM, count)):
                        # Search for collisions in outputs between the gcm instances
                        for i in range(2):
                            print("-" * 80)
                            print(
                                "Applying instruction skip in ", pc, "occurence", i_count, "data", i
                            )
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
                                symfi.handle_gcm(
                                    data[i],
                                    data_len,
                                    key,
                                    key_len,
                                    aad,
                                    aad_len,
                                    tag,
                                    tag_len,
                                    iv[i],
                                    cfg,
                                    trigger,
                                )
                                testos_response = read_testos_output()

                                gdb_response = gdb.read_output()
                                gcm_out[i] = None
                                if "instruction skip applied" in gdb_response:
                                    total_attacks += 1

                                    if crash_observation in gdb_response:
                                        print("Crash detected, resetting", flush=True)
                                        gdb = reset_target_and_gdb(gdb)
                                    else:
                                        testos_response_json = json.loads(testos_response)
                                        print("Output:", testos_response_json, flush=True)
                                        if testos_response_json["status"] == 0:
                                            gcm_out[i] = testos_response_json["data"]

                                            if gcm_out[i] == gcm_out[1 - i]:
                                                successful_faults += 1
                                                print("-" * 80)
                                                print("Successful FI attack!")
                                                print("Location:", pc, "iteration", i_count)
                                                print(gdb_response)
                                                print("Response:", testos_response_json)
                                                print("-" * 80)
                                        # Reset GDB by closing and opening again
                                        gdb = reset_gdb(gdb)
                                else:
                                    print("No break point found, something went wrong", flush=True)
                                    gdb = reset_target_and_gdb(gdb)

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
                print(f"Total attacks {total_attacks}, successful attacks {successful_faults}")
                # Close the OpenOCD and GDB connection at the end
                if gdb:
                    gdb.close_gdb()
                target.close_openocd()
                sys.stdout = original_stdout
                self.assertEqual(successful_faults, 0)
                self.assertEqual(started, True)


if __name__ == "__main__":
    r = Runfiles.Create()
    # Get the openocd path.
    openocd_path = r.Rlocation("lowrisc_opentitan/third_party/openocd/build_openocd/bin/openocd")
    # Get the openocd config files.
    # The config file for jtag
    CONFIG_FILE_CHIP = r.Rlocation("openocd/tcl/interface/cmsis-dap.cfg")
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
    symfi = OTFISymCrypto(target)
    parser = DisParser(dis_path)

    print("Disassembly is found in ", dis_path, flush=True)

    unittest.main(argv=[sys.argv[0]])
