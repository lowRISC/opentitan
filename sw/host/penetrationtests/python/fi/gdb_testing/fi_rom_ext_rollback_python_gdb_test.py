# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# What to do when running into errors:
# - If device is busy or seeing "rejected 'gdb' connection, no more connections allowed",
# cut the USB connection, e.g., sudo fuser /dev/ttyUSB0 and kill the PID
# - If the port is busy check sudo lsof -i :3333 and then kill the PID

from python.runfiles import Runfiles
from sw.host.penetrationtests.python.util import targets
from sw.host.penetrationtests.python.util.gdb_controller import GDBController
from sw.host.penetrationtests.python.util.dis_parser import DisParser
from collections import Counter
import argparse
import unittest
import sys
import os
import time
import signal
import serial

ignored_keys_set = set(["status"])
opentitantool_path = ""
log_dir = ""
rom_ext_elf_path = ""
rom_elf_path = ""
rom_ext_parser = None
rom_parser = None
target = None

# We set to only apply instruction skips in the first
# MAX_SKIPS_PER_LOOP iterations of a loop
MAX_SKIPS_PER_LOOP = 2

# Read in the extra arguments from the opentitan_test.
parser = argparse.ArgumentParser()
parser.add_argument("--bitstream", type=str)
parser.add_argument("--bootstrap", type=str)
parser.add_argument("--rom_ext", type=str)
parser.add_argument("--rom", type=str)

args, config_args = parser.parse_known_args()

BITSTREAM = args.bitstream
BOOTSTRAP = args.bootstrap
ROM_EXT = args.rom_ext
ROM = args.rom

original_stdout = sys.stdout


class IterationTimeout:
    def __init__(self, seconds, error_message="Iteration timed out"):
        self.seconds = seconds
        self.error_message = error_message

    def handle_timeout(self, signum, frame):
        raise TimeoutError(self.error_message)

    def __enter__(self):
        signal.signal(signal.SIGALRM, self.handle_timeout)
        signal.alarm(self.seconds)

    def __exit__(self, type, value, traceback):
        signal.alarm(0)


def read_uart_output():
    # Read the output from the chip
    response = target.read_all(max_tries=100)
    return response


def reset_target_and_gdb(gdb, jump_address, print_output=False):
    gdb.close_gdb()
    target.start_openocd(startup_delay=0.2, print_output=False)
    gdb = GDBController(gdb_path=GDB_PATH, gdb_port=GDB_PORT, elf_file=rom_ext_elf_path)
    gdb.reset_target()
    gdb.send_command(f"set $pc={jump_address}")
    target.dump_all()
    return gdb


# Only called when we encounter an issue where we want to re-flash everything
def re_initialize(gdb, jump_address, print_output=False):
    gdb.close_gdb()
    target.close_openocd()
    target.clear_bitstream()
    target.initialize_target(print_output=print_output)
    gdb = GDBController(gdb_path=GDB_PATH, gdb_port=GDB_PORT, elf_file=rom_ext_elf_path)
    gdb.reset_target()
    gdb.send_command(f"set $pc={jump_address}")
    target.dump_all()
    return gdb


class RomExtFiSimRollback(unittest.TestCase):
    def test_rom_ext_rollback(self):
        print("Starting the rom_ext secure boot test")

        # Directory for the trace log files
        pc_trace_file = os.path.join(log_dir, "rom_ext_rollback_pc_trace.log")
        # Directory for the the log of the campaign
        campaign_file = os.path.join(log_dir, "rom_ext_rollback_test_campaign.log")

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

                # We set the RMA spin cycles to a long timeout to be able to halt before ROM starts.
                # Jump over the spin cycles
                jump_address = rom_parser.get_function_start_address("kRomStartRmaSpinSkip")

                # Connect to GDB
                gdb = GDBController(gdb_path=GDB_PATH, gdb_port=GDB_PORT, elf_file=rom_ext_elf_path)

                # Reset the device and halt it immediately
                gdb.reset_target()
                gdb.send_command(f"set $pc={jump_address}")

                # We perform the tracing over the rom_ext_start function
                trace_start_address = rom_ext_parser.get_inlined_function_address("rom_ext_start")
                # We expect with the test that we end up in shutdown
                trace_end_address = rom_ext_parser.get_function_start_address("shutdown_finalize")

                print(
                    "Start and stop addresses for the rom_ext: ",
                    trace_start_address,
                    trace_end_address,
                    flush=True,
                )
                print("Trace data is logged in ", pc_trace_file, flush=True)

                # Start the tracing
                # We set a short timeout to detect whether GDB has connected properly
                # and a long timeout for the entire tracing
                initial_timeout = 20
                total_timeout = 60 * 60 * 5

                gdb.setup_pc_trace(
                    pc_trace_file,
                    trace_start_address,
                    trace_end_address,
                )
                gdb.send_command("c", check_response=False)

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
                gdb = reset_target_and_gdb(gdb, jump_address)

                started = True
                for pc, count in pc_count_dict.items():
                    for i_count in range(min(MAX_SKIPS_PER_LOOP, count)):
                        print("-" * 80)
                        print("Applying instruction skip in ", pc, "occurence", i_count)
                        print("-" * 80)

                        try:
                            # If we have a timeout, we continue to the next iteration
                            with IterationTimeout(seconds=60):
                                gdb.apply_instruction_skip(
                                    pc, rom_ext_parser.parse_next_instruction(pc), i_count
                                )
                                gdb.send_command("c", check_response=False)

                                response = read_uart_output()
                                gdb_response = gdb.read_output()

                                if "instruction skip applied" in gdb_response:
                                    total_attacks += 1

                                    print("Output:", response, flush=True)

                                    if "Running" in response:
                                        successful_faults += 1
                                        print("-" * 80)
                                        print("Successful FI attack!")
                                        print("Location:", pc, "iteration", i_count)
                                        print(gdb_response)
                                        print("Response:", response)
                                        print("-" * 80)

                                        try:
                                            gdb = reset_target_and_gdb(gdb, jump_address)
                                        except TimeoutError:
                                            print("Timeout, reflashing", flush=True)
                                            gdb = re_initialize(gdb, jump_address)
                                    elif "saved" in response:
                                        # Here we know that something was changed in flash
                                        print("Seeing a flash change, reflashing", flush=True)
                                        gdb = re_initialize(gdb, jump_address)
                                    else:
                                        try:
                                            gdb = reset_target_and_gdb(gdb, jump_address)
                                        except TimeoutError:
                                            print("Timeout, reflashing", flush=True)
                                            gdb = re_initialize(gdb, jump_address)
                                else:
                                    print("No break point found, something went wrong", flush=True)
                                    # Just to be safe that nothing went into flash, we reflash
                                    gdb = re_initialize(gdb, jump_address)

                        except (TimeoutError, serial.SerialException) as e:
                            print("Timeout error, retrying", flush=True)
                            print(e, flush=True)
                            signal.alarm(0)
                            gdb = re_initialize(gdb, jump_address)

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
    # Get the rom path.
    rom_path = r.Rlocation("lowrisc_opentitan/" + ROM)
    # Get the disassembly path.
    rom_dis_path = rom_path.replace(".39.scr.vmem", ".dis")
    # And the path for the elf.
    rom_elf_path = rom_path.replace(".39.scr.vmem", ".elf")
    # Get the rom_ext path.
    rom_ext_path = r.Rlocation("lowrisc_opentitan/" + ROM_EXT)
    # Get the disassembly path.
    rom_ext_dis_path = rom_ext_path.replace(".prod_key_0.signed.bin", ".dis")
    # And the path for the elf.
    rom_ext_elf_path = rom_ext_path.replace(".prod_key_0.signed.bin", ".elf")

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
    rom_ext_parser = DisParser(rom_ext_dis_path)
    rom_parser = DisParser(rom_dis_path)

    print("ROM disassembly is found in ", rom_dis_path, flush=True)
    print("ROM_EXT disassembly is found in ", rom_ext_dis_path, flush=True)

    unittest.main(argv=[sys.argv[0]])
