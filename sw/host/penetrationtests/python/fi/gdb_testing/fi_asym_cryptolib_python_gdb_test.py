# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from sw.host.penetrationtests.python.fi.communication.fi_asym_cryptolib_commands import (
    OTFIAsymCrypto,
)
from python.runfiles import Runfiles
from sw.host.penetrationtests.python.util import targets
from sw.host.penetrationtests.python.util import common_library
from sw.host.penetrationtests.python.util.gdb_controller import GDBController
import json
import argparse
import sys
import os
import time
from Crypto.PublicKey import ECC
from Crypto.Signature import DSS
from Crypto.Hash import SHA384

ignored_keys_set = set(["status"])
opentitantool_path = ""

target = None
asymfi = None

# Read in the extra arguments from the opentitan_test.
parser = argparse.ArgumentParser()
parser.add_argument("--bitstream", type=str)
parser.add_argument("--bootstrap", type=str)

args, config_args = parser.parse_known_args()

BITSTREAM = args.bitstream
BOOTSTRAP = args.bootstrap


# Preparing the input for an invalid signature
key = ECC.generate(curve="P-384")
pubx = [x for x in key.pointQ.x.to_bytes(48, "little")]
puby = [x for x in key.pointQ.y.to_bytes(48, "little")]
message = [i for i in range(16)]
h = SHA384.new(bytes(message))
signer = DSS.new(key, "fips-186-3")
signature = [x for x in signer.sign(h)]
# Corrupted the signature for FiSim Testing
signature[0] ^= 0x1
r_bytes = signature[:48]
s_bytes = signature[48:]
r_bytes.reverse()
s_bytes.reverse()
cfg = 0
trigger = 1
h = SHA384.new(bytes(message))
message_digest = [x for x in h.digest()]


def trigger_testos_init(print_output=True):
    # Initializing the testOS (setting up the alerts and accelerators)
    (
        device_id,
        sensors,
        alerts,
        owner_page,
        boot_log,
        boot_measurements,
        version,
    ) = asymfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    if print_output:
        print("Output from init ", device_id)


def trigger_p384_verify():
    asymfi.handle_p384_verify(pubx, puby, r_bytes, s_bytes, message_digest, cfg, trigger)


def read_testos_output():
    # Read the output from the operation
    response = target.read_response(max_tries=500)
    return response


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
    # Directory for the trace log files
    log_dir = os.environ.get("TEST_UNDECLARED_OUTPUTS_DIR")
    pc_trace_file = os.path.join(log_dir, "pc_trace.log")
    # Directory for the output results
    test_results_file = os.path.join(log_dir, "test_results.log")
    # Program the bitstream for FPGAs.
    bitstream_path = None
    if BITSTREAM:
        bitstream_path = r.Rlocation("lowrisc_opentitan/" + BITSTREAM)
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
    successful_faults = 0
    total_attacks = 0

    # How to read outputs in this script:
    # To view the UART output from the testOS or the chip in general, use:
    # target.print_all() or print(read_testos_output())
    # In order to print the OpenOCD output use print(target.read_openocd())
    # In order to print the output from GDB use print(gdb.read_output()) or
    # when you want to know the output from a gdb.send_command() print it:
    # print(gdb.send_command())

    # What to do when running into errors:
    # - If device is busy or seeing "rejected 'gdb' connection, no more connections allowed",
    # cut the USB connection, e.g., sudo fuser /dev/ttyUSB0 and kill the PID
    # - If the port is busy check sudo lsof -i :6666 and then kill the PID

    try:
        # Program the bitstream, flash the target, and set up OpenOCD
        target.initialize_target()

        # Initialize the testOS
        trigger_testos_init()

        # Connect to GDB
        gdb = GDBController(gdb_path=GDB_PATH, gdb_port=GDB_PORT, elf_file=elf_path)

        # Provide the function name and extract the start and end address from the dis file
        function_name = "OUTLINED_FUNCTION_22"
        # otcrypto_ecdsa_p384_verify (second one)
        # OUTLINED_FUNCTION_22 (second one)
        # hardened_memeq (not working yet)
        # p384_scalar_write (any one)
        # Gives back an array of hits where the function is called
        trace_addresses = gdb.get_function_addresses(dis_path, function_name)
        print(
            "Start and stop addresses of ",
            function_name,
            ": ",
            trace_addresses,
            flush=True,
        )

        p384_observation_addresses = gdb.get_function_addresses(
            dis_path, "otcrypto_ecdsa_p384_verify"
        )
        crash_observation_address = gdb.get_function_start_address(
            dis_path, "ottf_exception_handler"
        )

        # Start the tracing
        # We set a long timeout
        timeout = 60 * 1
        # We pick the second address hit
        # TODO: Find a way to pick the correct one
        # If we pick the wrong one, we get a timeout

        gdb.setup_pc_trace(pc_trace_file, trace_addresses[1][0], trace_addresses[1][1])
        gdb.send_command("c", check_response=False)

        # Trigger the p384 verify from the testOS (we do not read its output)
        trigger_p384_verify()

        start_time = time.time()
        stopped = False

        # Run the tracing to get the trace log
        while time.time() - start_time < timeout:
            output = gdb.read_output(timeout=0.5)
            if "PC trace complete" in output:
                print("\nTrace complete", flush=True)
                stopped = True
                break
        if not stopped:
            print("No final break point found, stopping")
            sys.exit(1)

        # Parse and truncate the trace log to get all PCs in a list
        pc_list = gdb.parse_pc_trace_file(pc_trace_file)

        # TODO: Make this truncate for wait cycles and identify the instance count ...
        # Get only the unique addresses
        pc_list = list(set(pc_list))
        print("Tracing has a total of", len(pc_list), "PCs", flush=True)

        if len(pc_list) <= 0:
            print("Found no tracing, stopping")
            sys.exit(1)

        # Reset the target, flush the output, and close gdb
        gdb.reset_target()
        target.dump_all()
        trigger_testos_init(print_output=False)
        gdb.close_gdb()
        gdb = GDBController(gdb_path=GDB_PATH, gdb_port=GDB_PORT, elf_file=elf_path)

        # Open the results file
        test_results = open(test_results_file, "w")

        idx = 0
        while idx < len(pc_list):
            print("-" * 80)
            print("Applying instruction skip in ", pc_list[idx], flush=True)
            print("-" * 80)

            prefix_observation = "fisim_result:"
            function_output_observation = "function output detected"
            crash_observation = "crash detected"

            # TODO Adding the observation points create a problem in the flow of the instructions
            # The observation points
            # observations = {
            #     # Function output
            #     p384_observation_addresses[1][1]: f"{function_output_observation}",
            #     # Crash check
            #     crash_observation_address: f"{crash_observation}",
            # }
            # gdb.add_observation(observations)

            # TODO Handle multiple same addresses
            gdb.apply_instruction_skip(
                pc_list[idx], gdb.parse_next_instruction(pc_list[idx], dis_path)
            )
            gdb.send_command("c", check_response=False)

            # The instruction skip loop
            trigger_p384_verify()
            time.sleep(0.02)
            testos_response = read_testos_output()
            try:
                gdb_response = gdb.read_output()
                if (
                    'stopped,reason="breakpoint-hit"' in gdb_response
                    and "instruction skip applied" in gdb_response
                ):
                    idx += 1
                    total_attacks += 1
                    testos_response_json = json.loads(testos_response)
                    print("Output:", testos_response_json)
                    verification_result = testos_response_json["result"]
                    if verification_result == "true":
                        successful_faults += 1
                        print("-" * 80, flush=True)
                        print("Successful FI attack!", flush=True)
                        print("Location:", pc_list[idx], flush=True)
                        print(gdb_response, flush=True)
                        print("Response:", testos_response_json)
                        print("-" * 80, flush=True)
                        test_results.write(f"{pc_list[idx]}: {testos_response_json}\n")

                    # Reset GDB by closing and opening again
                    gdb.close_gdb()
                    gdb = GDBController(gdb_path=GDB_PATH, gdb_port=GDB_PORT, elf_file=elf_path)
                    # We do not need to reset the target since it returned an output
                else:
                    print("No break point found, something went wrong", flush=True)
                    gdb.close_gdb()
                    gdb = GDBController(gdb_path=GDB_PATH, gdb_port=GDB_PORT, elf_file=elf_path)
                    gdb.reset_target()
                    target.dump_all()
                    trigger_testos_init(print_output=False)
                    # Reset again
                    gdb.close_gdb()
                    gdb = GDBController(gdb_path=GDB_PATH, gdb_port=GDB_PORT, elf_file=elf_path)

            except json.JSONDecodeError:
                print("Error: JSON decoding failed. Invalid response format.", flush=True)
                gdb.close_gdb()
                gdb = GDBController(gdb_path=GDB_PATH, gdb_port=GDB_PORT, elf_file=elf_path)
                gdb.reset_target()
                target.dump_all()
                trigger_testos_init(print_output=False)
                # Reset again
                gdb.close_gdb()
                gdb = GDBController(gdb_path=GDB_PATH, gdb_port=GDB_PORT, elf_file=elf_path)

    finally:
        print("-" * 80)
        print("Trace data is logged in ", pc_trace_file, flush=True)
        print("Instruction skip results are logged in ", test_results_file, flush=True)
        print(
            f"Total attacks {total_attacks}, successful attacks {successful_faults}",
            flush=True,
        )
        print("You can find the dissassembly in ", dis_path, flush=True)
        # Close the OpenOCD and GDB connection at the end
        target.close_openocd()
