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
MAX_SKIPS_PER_LOOP = 3

target = None
symfi = None

# Read in the extra arguments from the opentitan_test.
parser = argparse.ArgumentParser()
parser.add_argument("--bitstream", type=str)
parser.add_argument("--bootstrap", type=str)

args, config_args = parser.parse_known_args()

BITSTREAM = args.bitstream
BOOTSTRAP = args.bootstrap


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
        # Directory for the output results
        test_results_file = os.path.join(log_dir, "hmac_test_results.log")
        # Directory for the the log of the campaign
        campaign_file = os.path.join(log_dir, "hmac_test_campaign.log")

        successful_faults = 0
        total_attacks = 0

        def trigger_testos_init(print_output=True):
            # Initializing the testOS (setting up the alerts and accelerators)
            (device_id, _, _, _, _, _, _) = symfi.init(
                alert_config=common_library.no_escalation_alert_config
            )
            if print_output:
                print("Output from init ", device_id)

        def trigger_hmac(i):
            symfi.handle_hmac(data[i], data_len, key, key_len, hash_mode, mode, cfg, trigger)

        def read_testos_output():
            # Read the output from the operation
            response = target.read_response(max_tries=500)
            return response

        hmac1_outputs = []
        hmac2_outputs = []
        hmac_outputs = [hmac1_outputs, hmac2_outputs]

        gdb = None
        started = False
        with open(test_results_file, "w") as test_results, open(campaign_file, "w") as campaign:
            try:
                # Program the bitstream, flash the target, and set up OpenOCD
                target.initialize_target()

                # Initialize the testOS
                trigger_testos_init()

                # Connect to GDB
                gdb = GDBController(gdb_path=GDB_PATH, gdb_port=GDB_PORT, elf_file=elf_path)

                # Provide the function name and extract the start and end address from the dis file
                function_name = "otcrypto_hmac"
                # Gives back an array of hits where the function is called
                trace_addresses = parser.get_function_addresses(function_name)
                print("Start and stop addresses of ", function_name, ": ", trace_addresses)

                for trace_address in trace_addresses:
                    if not parser.is_trigger_in_function_of_address(trace_address[0]):
                        print("Address", trace_address[0], " does not contain a trigger function")
                        continue

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
                    trigger_hmac(0)

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
                    campaign.write(f"Tracing has a total of {len(pc_count_dict)} unique PCs\n")

                    # Reset the target, flush the output, and close gdb
                    gdb.reset_target()
                    target.dump_all()
                    trigger_testos_init(print_output=False)
                    gdb.close_gdb()
                    gdb = GDBController(gdb_path=GDB_PATH, gdb_port=GDB_PORT, elf_file=elf_path)

                    started = True
                    for pc, count in pc_count_dict.items():
                        i_count = 0
                        while i_count < min(MAX_SKIPS_PER_LOOP, count):
                            # Search for collisions in outputs between the HMAC instances
                            for i in range(2):
                                print("-" * 80)
                                print("Applying instruction skip in ", pc, "occurence", i_count)
                                print("-" * 80)
                                campaign.write(
                                    f"Applying instruction skip in {pc} occurence {i_count}\n"
                                )

                                function_output_observation = "function output detected"
                                crash_observation = "crash detected"

                                try:
                                    # The observation points
                                    observations = {
                                        # Function output
                                        trace_address[1]: f"{function_output_observation}",
                                        # Crash check
                                        crash_observation_address: f"{crash_observation}",
                                    }
                                    gdb.add_observation(observations)

                                    gdb.apply_instruction_skip(
                                        pc, parser.parse_next_instruction(pc), i_count
                                    )
                                    gdb.send_command("c", check_response=False)

                                    # The instruction skip loop
                                    trigger_hmac(i)
                                    testos_response = read_testos_output()

                                    gdb_response = gdb.read_output()
                                    if "instruction skip applied" in gdb_response:
                                        i_count += 1
                                        total_attacks += 1

                                        if crash_observation in gdb_response:
                                            print("Crash detected, resetting", flush=True)
                                            campaign.write("Crash detected, resetting\n")
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
                                        elif function_output_observation in gdb_response:
                                            testos_response_json = json.loads(testos_response)
                                            print("Output:", testos_response_json, flush=True)
                                            campaign.write(f"Output: {testos_response_json}\n")
                                            data_out = testos_response_json["data"]
                                            hmac_outputs[i].append(data_out)

                                            if data_out in hmac_outputs[1 - i]:
                                                successful_faults += 1
                                                print("-" * 80)
                                                print("Successful FI attack!")
                                                print("Location:", pc, "iteration", i_count - 1)
                                                print(gdb_response)
                                                print("Response:", testos_response_json)
                                                print()
                                                print("Content of hmac_outputs[0]")
                                                print(hmac_outputs[0])
                                                print()
                                                print("Content of hmac_outputs[1]")
                                                print(hmac_outputs[1])
                                                print("-" * 80)
                                                test_results.write(
                                                    f"{pc}, {i_count - 1}: {testos_response_json}\n"
                                                )
                                            # Reset GDB by closing and opening again
                                            gdb.close_gdb()
                                            gdb = GDBController(
                                                gdb_path=GDB_PATH,
                                                gdb_port=GDB_PORT,
                                                elf_file=elf_path,
                                            )
                                        else:
                                            print(
                                                "Firmware behaved unexpected, no crash or output",
                                                flush=True,
                                            )
                                            campaign.write(
                                                "Firmware behaved unexpected, no crash or output\n"
                                            )
                                            gdb.close_gdb()
                                            target.close_openocd()
                                            time.sleep(0.5)
                                            target.initialize_target()
                                            trigger_testos_init()
                                            target.dump_all()
                                            gdb = GDBController(
                                                gdb_path=GDB_PATH,
                                                gdb_port=GDB_PORT,
                                                elf_file=elf_path,
                                            )
                                            time.sleep(2)
                                    else:
                                        print(
                                            "No break point found, something went wrong", flush=True
                                        )
                                        campaign.write(
                                            "No break point found, something went wrong\n"
                                        )
                                        gdb.close_gdb()
                                        target.close_openocd()
                                        time.sleep(0.5)
                                        target.initialize_target()
                                        trigger_testos_init()
                                        target.dump_all()
                                        gdb = GDBController(
                                            gdb_path=GDB_PATH, gdb_port=GDB_PORT, elf_file=elf_path
                                        )
                                        time.sleep(2)

                                except json.JSONDecodeError:
                                    print(
                                        "Error: JSON decoding failed. Invalid response format",
                                        flush=True,
                                    )
                                    campaign.write(
                                        "Error: JSON decoding failed. Invalid response format\n"
                                    )
                                    gdb.close_gdb()
                                    gdb = GDBController(
                                        gdb_path=GDB_PATH, gdb_port=GDB_PORT, elf_file=elf_path
                                    )
                                    gdb.reset_target()
                                    target.dump_all()
                                    trigger_testos_init(print_output=False)
                                    # Reset again
                                    gdb.close_gdb()
                                    gdb = GDBController(
                                        gdb_path=GDB_PATH, gdb_port=GDB_PORT, elf_file=elf_path
                                    )

                                except TimeoutError as e:
                                    print("Timeout error, retrying", flush=True)
                                    campaign.write("Timeout error, retrying\n")
                                    print(e, flush=True)
                                    gdb.close_gdb()
                                    target.close_openocd()
                                    time.sleep(0.5)
                                    target.initialize_target()
                                    trigger_testos_init()
                                    target.dump_all()
                                    gdb = GDBController(
                                        gdb_path=GDB_PATH, gdb_port=GDB_PORT, elf_file=elf_path
                                    )
                                    time.sleep(2)

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
                test_results.write("Content of hmac_outputs[0]\n")
                test_results.write(f"{hmac_outputs[0]}\n")
                test_results.write("Content of hmac_outputs[1]\n")
                test_results.write(f"{hmac_outputs[1]}\n")
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
        iv = [i for i in range(16)]
        cfg = 0
        trigger = 0

        # Directory for the trace log files
        pc_trace_file = os.path.join(log_dir, "gcm_pc_trace.log")
        # Directory for the output results
        test_results_file = os.path.join(log_dir, "gcm_test_results.log")
        # Directory for the the log of the campaign
        campaign_file = os.path.join(log_dir, "gcm_test_campaign.log")

        successful_faults = 0
        total_attacks = 0

        def trigger_testos_init(print_output=True):
            # Initializing the testOS (setting up the alerts and accelerators)
            (device_id, _, _, _, _, _, _) = symfi.init(
                alert_config=common_library.no_escalation_alert_config
            )
            if print_output:
                print("Output from init ", device_id)

        def trigger_gcm(i):
            symfi.handle_gcm(
                data[i],
                data_len,
                key,
                key_len,
                aad,
                aad_len,
                tag,
                tag_len,
                iv,
                cfg,
                trigger,
            )

        def read_testos_output():
            # Read the output from the operation
            response = target.read_response(max_tries=500)
            return response

        gcm1_tags = []
        gcm2_tags = []
        gcm_tags = [gcm1_tags, gcm2_tags]

        gdb = None
        started = False
        with open(test_results_file, "w") as test_results, open(campaign_file, "w") as campaign:
            try:
                # Program the bitstream, flash the target, and set up OpenOCD
                target.initialize_target()

                # Initialize the testOS
                trigger_testos_init()

                # Connect to GDB
                gdb = GDBController(gdb_path=GDB_PATH, gdb_port=GDB_PORT, elf_file=elf_path)

                # Provide the function name and extract the start and end address from the dis file
                function_name = "otcrypto_aes_gcm_encrypt"
                # Gives back an array of hits where the function is called
                trace_addresses = parser.get_function_addresses(function_name)
                print("Start and stop addresses of ", function_name, ": ", trace_addresses)

                for trace_address in trace_addresses:
                    if not parser.is_trigger_in_function_of_address(trace_address[0]):
                        print("Address", trace_address[0], " does not contain a trigger function")
                        continue

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

                    # Trigger the gcm from the testOS (we do not read its output)
                    trigger_gcm(0)

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
                    campaign.write(f"Tracing has a total of {len(pc_count_dict)} unique PCs\n")

                    # Reset the target, flush the output, and close gdb
                    gdb.reset_target()
                    target.dump_all()
                    trigger_testos_init(print_output=False)
                    gdb.close_gdb()
                    gdb = GDBController(gdb_path=GDB_PATH, gdb_port=GDB_PORT, elf_file=elf_path)

                    started = True
                    for pc, count in pc_count_dict.items():
                        i_count = 0
                        while i_count < min(MAX_SKIPS_PER_LOOP, count):
                            # Search for collisions in outputs between the gcm instances
                            for i in range(2):
                                print("-" * 80)
                                print("Applying instruction skip in ", pc, "occurence", i_count)
                                print("-" * 80)
                                campaign.write(
                                    f"Applying instruction skip in {pc} occurence {i_count}\n"
                                )

                                function_output_observation = "function output detected"
                                crash_observation = "crash detected"

                                try:
                                    # The observation points
                                    observations = {
                                        # Function output
                                        trace_address[1]: f"{function_output_observation}",
                                        # Crash check
                                        crash_observation_address: f"{crash_observation}",
                                    }
                                    gdb.add_observation(observations)

                                    gdb.apply_instruction_skip(
                                        pc, parser.parse_next_instruction(pc), i_count
                                    )
                                    gdb.send_command("c", check_response=False)

                                    # The instruction skip loop
                                    trigger_gcm(i)
                                    testos_response = read_testos_output()

                                    gdb_response = gdb.read_output()
                                    if "instruction skip applied" in gdb_response:
                                        i_count += 1
                                        total_attacks += 1

                                        if crash_observation in gdb_response:
                                            print("Crash detected, resetting", flush=True)
                                            campaign.write("Crash detected, resetting\n")
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
                                        elif function_output_observation in gdb_response:
                                            testos_response_json = json.loads(testos_response)
                                            print("Output:", testos_response_json, flush=True)
                                            campaign.write(f"Output: {testos_response_json}\n")
                                            tag_out = testos_response_json["tag"]
                                            gcm_tags[i].append(tag_out)

                                            if tag_out in gcm_tags[1 - i]:
                                                successful_faults += 1
                                                print("-" * 80)
                                                print("Successful FI attack!")
                                                print("Location:", pc, "iteration", i_count - 1)
                                                print(gdb_response)
                                                print("Response:", testos_response_json)
                                                print()
                                                print("Content of gcm_tags[0]")
                                                print(gcm_tags[0])
                                                print()
                                                print("Content of gcm_tags[1]")
                                                print(gcm_tags[1])
                                                print("-" * 80)
                                                test_results.write(
                                                    f"{pc}, {i_count - 1}: {testos_response_json}\n"
                                                )
                                            # Reset GDB by closing and opening again
                                            gdb.close_gdb()
                                            gdb = GDBController(
                                                gdb_path=GDB_PATH,
                                                gdb_port=GDB_PORT,
                                                elf_file=elf_path,
                                            )
                                        else:
                                            print(
                                                "Firmware behaved unexpected, no crash or output",
                                                flush=True,
                                            )
                                            campaign.write(
                                                "Firmware behaved unexpected, no crash or output\n"
                                            )
                                            gdb.close_gdb()
                                            target.close_openocd()
                                            time.sleep(0.5)
                                            target.initialize_target()
                                            trigger_testos_init()
                                            target.dump_all()
                                            gdb = GDBController(
                                                gdb_path=GDB_PATH,
                                                gdb_port=GDB_PORT,
                                                elf_file=elf_path,
                                            )
                                            time.sleep(2)
                                    else:
                                        print(
                                            "No break point found, something went wrong", flush=True
                                        )
                                        campaign.write(
                                            "No break point found, something went wrong\n"
                                        )
                                        gdb.close_gdb()
                                        target.close_openocd()
                                        time.sleep(0.5)
                                        target.initialize_target()
                                        trigger_testos_init()
                                        target.dump_all()
                                        gdb = GDBController(
                                            gdb_path=GDB_PATH, gdb_port=GDB_PORT, elf_file=elf_path
                                        )
                                        time.sleep(2)

                                except json.JSONDecodeError:
                                    print(
                                        "Error: JSON decoding failed. Invalid response format",
                                        flush=True,
                                    )
                                    campaign.write(
                                        "Error: JSON decoding failed. Invalid response format\n"
                                    )
                                    gdb.close_gdb()
                                    gdb = GDBController(
                                        gdb_path=GDB_PATH, gdb_port=GDB_PORT, elf_file=elf_path
                                    )
                                    gdb.reset_target()
                                    target.dump_all()
                                    trigger_testos_init(print_output=False)
                                    # Reset again
                                    gdb.close_gdb()
                                    gdb = GDBController(
                                        gdb_path=GDB_PATH, gdb_port=GDB_PORT, elf_file=elf_path
                                    )

                                except TimeoutError as e:
                                    print("Timeout error, retrying", flush=True)
                                    campaign.write("Timeout error, retrying\n")
                                    print(e, flush=True)
                                    gdb.close_gdb()
                                    target.close_openocd()
                                    time.sleep(0.5)
                                    target.initialize_target()
                                    trigger_testos_init()
                                    target.dump_all()
                                    gdb = GDBController(
                                        gdb_path=GDB_PATH, gdb_port=GDB_PORT, elf_file=elf_path
                                    )
                                    time.sleep(2)

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
                test_results.write("Content of gcm_tags[0]\n")
                test_results.write(f"{gcm_tags[0]}\n")
                test_results.write("Content of gcm_tags[1]\n")
                test_results.write(f"{gcm_tags[1]}\n")
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
    symfi = OTFISymCrypto(target)
    parser = DisParser(dis_path)

    unittest.main(argv=[sys.argv[0]])
