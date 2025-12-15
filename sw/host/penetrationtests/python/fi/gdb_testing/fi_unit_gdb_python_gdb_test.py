# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# What to do when running into errors:
# - If device is busy or seeing "rejected 'gdb' connection, no more connections allowed",
# cut the USB connection, e.g., sudo fuser /dev/ttyUSB0 and kill the PID
# - If the port is busy check sudo lsof -i :3333 and then kill the PID

from sw.host.penetrationtests.python.fi.communication.fi_unit_gdb_commands import (
    OTFIUnitGdb,
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

opentitantool_path = ""
log_dir = ""
elf_path = ""

# We set to only apply instruction skips in the first
# MAX_SKIPS_PER_LOOP iterations of a loop
MAX_SKIPS_PER_LOOP = 2

target = None
gdbfi = None

# Read in the extra arguments from the opentitan_test.
parser = argparse.ArgumentParser()
parser.add_argument("--bitstream", type=str)
parser.add_argument("--bootstrap", type=str)

args, config_args = parser.parse_known_args()

BITSTREAM = args.bitstream
BOOTSTRAP = args.bootstrap


def trigger_testos_init(print_output=False):
    # Initializing the testOS (setting up the alerts and accelerators)
    (device_id, _, _, _, _, _, _) = gdbfi.init(
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


class UnitFiSim(unittest.TestCase):
    def test_gdb_try(self):
        # Directory for the trace log files
        pc_trace_file = os.path.join(log_dir, "gdb_try_pc_trace.log")

        successful_faults = 0
        total_attacks = 0

        gdb = None
        started = False
        try:
            # Program the bitstream, flash the target, and set up OpenOCD
            target.initialize_target(print_output=False)

            # Initialize the testOS
            trigger_testos_init()

            # Connect to GDB
            gdb = GDBController(gdb_path=GDB_PATH, gdb_port=GDB_PORT, elf_file=elf_path)

            # We provide the name of the unique marker in the pentest framework
            function_name = "PENTEST_MARKER_GDB_TRY"
            # Gives back an array of hits where the function is called
            trace_address = parser.get_marker_addresses(function_name)

            crash_observation_address = parser.get_function_start_address("ottf_exception_handler")

            # Start the tracing
            # We set a short timeout to detect whether GDB has connected properly
            # and a long timeout for the entire tracing
            initial_timeout = 10
            total_timeout = 60 * 60 * 5

            gdb.setup_pc_trace(pc_trace_file, trace_address[0], trace_address[1])
            gdb.send_command("c", check_response=False)

            gdbfi.handle_gdb_try()

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

            # Reset the target, flush the output, and close gdb
            gdb = reset_target_and_gdb(gdb)

            started = True
            for pc, count in pc_count_dict.items():
                for i_count in range(min(MAX_SKIPS_PER_LOOP, count)):
                    crash_observation = "crash detected"

                    try:
                        # The observation points
                        observations = {
                            # Crash check
                            crash_observation_address: f"{crash_observation}",
                        }
                        gdb.add_observation(observations)

                        gdb.apply_instruction_skip(pc, parser.parse_next_instruction(pc), i_count)
                        gdb.send_command("c", check_response=False)

                        # The instruction skip loop
                        gdbfi.handle_gdb_try()
                        testos_response = read_testos_output()

                        gdb_response = gdb.read_output()
                        if "instruction skip applied" in gdb_response:
                            i_count += 1
                            total_attacks += 1

                            if crash_observation in gdb_response:
                                gdb = reset_target_and_gdb(gdb)
                            else:
                                testos_response_json = json.loads(testos_response)
                                if (testos_response_json["status"] == 0) and (
                                    not testos_response_json["result"]
                                ):
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
                            gdb = reset_target_and_gdb(gdb)

                    except json.JSONDecodeError:
                        try:
                            gdb = reset_target_and_gdb(gdb)
                        except TimeoutError:
                            gdb = re_initialize(gdb)

                    except TimeoutError:
                        try:
                            gdb = reset_target_and_gdb(gdb)
                        except TimeoutError:
                            gdb = re_initialize(gdb)

        finally:
            # Close the OpenOCD and GDB connection at the end
            if gdb:
                gdb.close_gdb()
            target.close_openocd()
            self.assertEqual(successful_faults, 0)
            self.assertEqual(started, True)

    def test_gdb_switch(self):
        # Directory for the trace log files
        pc_trace_file = os.path.join(log_dir, "gdb_switch_pc_trace.log")

        successful_faults = 0
        total_attacks = 0

        gdb = None
        started = False
        try:
            # Program the bitstream, flash the target, and set up OpenOCD
            target.initialize_target(print_output=False)

            # Initialize the testOS
            trigger_testos_init()

            # Connect to GDB
            gdb = GDBController(gdb_path=GDB_PATH, gdb_port=GDB_PORT, elf_file=elf_path)

            # We provide the name of the unique marker in the pentest framework
            function_name = "PENTEST_MARKER_GDB_SWITCH"
            # Gives back an array of hits where the function is called
            trace_address = parser.get_marker_addresses(function_name)

            crash_observation_address = parser.get_function_start_address("ottf_exception_handler")

            # Start the tracing
            # We set a short timeout to detect whether GDB has connected properly
            # and a long timeout for the entire tracing
            initial_timeout = 10
            total_timeout = 60 * 60 * 5

            gdb.setup_pc_trace(pc_trace_file, trace_address[0], trace_address[1])
            gdb.send_command("c", check_response=False)

            gdbfi.handle_gdb_switch()

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

            # Reset the target, flush the output, and close gdb
            gdb = reset_target_and_gdb(gdb)

            started = True
            for pc, count in pc_count_dict.items():
                for i_count in range(min(MAX_SKIPS_PER_LOOP, count)):
                    crash_observation = "crash detected"

                    try:
                        # The observation points
                        observations = {
                            # Crash check
                            crash_observation_address: f"{crash_observation}",
                        }
                        gdb.add_observation(observations)

                        gdb.apply_instruction_skip(pc, parser.parse_next_instruction(pc), i_count)
                        gdb.send_command("c", check_response=False)

                        # The instruction skip loop
                        gdbfi.handle_gdb_switch()
                        testos_response = read_testos_output()

                        gdb_response = gdb.read_output()
                        if "instruction skip applied" in gdb_response:
                            i_count += 1
                            total_attacks += 1

                            if crash_observation in gdb_response:
                                gdb = reset_target_and_gdb(gdb)
                            else:
                                testos_response_json = json.loads(testos_response)
                                if (testos_response_json["status"] == 0) and (
                                    not testos_response_json["result"]
                                ):
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
                            gdb = reset_target_and_gdb(gdb)

                    except json.JSONDecodeError:
                        try:
                            gdb = reset_target_and_gdb(gdb)
                        except TimeoutError:
                            gdb = re_initialize(gdb)

                    except TimeoutError:
                        try:
                            gdb = reset_target_and_gdb(gdb)
                        except TimeoutError:
                            gdb = re_initialize(gdb)

        finally:
            # Close the OpenOCD and GDB connection at the end
            if gdb:
                gdb.close_gdb()
            target.close_openocd()
            self.assertEqual(successful_faults, 0)
            self.assertEqual(started, True)

    def test_gdb_if(self):
        # Directory for the trace log files
        pc_trace_file = os.path.join(log_dir, "gdb_if_pc_trace.log")

        successful_faults = 0
        total_attacks = 0

        gdb = None
        started = False
        try:
            # Program the bitstream, flash the target, and set up OpenOCD
            target.initialize_target(print_output=False)

            # Initialize the testOS
            trigger_testos_init()

            # Connect to GDB
            gdb = GDBController(gdb_path=GDB_PATH, gdb_port=GDB_PORT, elf_file=elf_path)

            # We provide the name of the unique marker in the pentest framework
            function_name = "PENTEST_MARKER_GDB_IF"
            # Gives back an array of hits where the function is called
            trace_address = parser.get_marker_addresses(function_name)

            crash_observation_address = parser.get_function_start_address("ottf_exception_handler")

            # Start the tracing
            # We set a short timeout to detect whether GDB has connected properly
            # and a long timeout for the entire tracing
            initial_timeout = 10
            total_timeout = 60 * 60 * 5

            gdb.setup_pc_trace(pc_trace_file, trace_address[0], trace_address[1])
            gdb.send_command("c", check_response=False)

            gdbfi.handle_gdb_if()

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

            # Reset the target, flush the output, and close gdb
            gdb = reset_target_and_gdb(gdb)

            started = True
            for pc, count in pc_count_dict.items():
                for i_count in range(min(MAX_SKIPS_PER_LOOP, count)):
                    crash_observation = "crash detected"

                    try:
                        # The observation points
                        observations = {
                            # Crash check
                            crash_observation_address: f"{crash_observation}",
                        }
                        gdb.add_observation(observations)

                        gdb.apply_instruction_skip(pc, parser.parse_next_instruction(pc), i_count)
                        gdb.send_command("c", check_response=False)

                        # The instruction skip loop
                        gdbfi.handle_gdb_if()
                        testos_response = read_testos_output()

                        gdb_response = gdb.read_output()
                        if "instruction skip applied" in gdb_response:
                            i_count += 1
                            total_attacks += 1

                            if crash_observation in gdb_response:
                                gdb = reset_target_and_gdb(gdb)
                            else:
                                testos_response_json = json.loads(testos_response)
                                if (testos_response_json["status"] == 0) and (
                                    not testos_response_json["result"]
                                ):
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
                            gdb = reset_target_and_gdb(gdb)

                    except json.JSONDecodeError:
                        try:
                            gdb = reset_target_and_gdb(gdb)
                        except TimeoutError:
                            gdb = re_initialize(gdb)

                    except TimeoutError:
                        try:
                            gdb = reset_target_and_gdb(gdb)
                        except TimeoutError:
                            gdb = re_initialize(gdb)

        finally:
            # Close the OpenOCD and GDB connection at the end
            if gdb:
                gdb.close_gdb()
            target.close_openocd()
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
    gdbfi = OTFIUnitGdb(target)
    parser = DisParser(dis_path)

    unittest.main(argv=[sys.argv[0]])
