# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import Optional
from subprocess import PIPE, Popen, TimeoutExpired
import select
import signal
import os
import time
import re


class GDBController:
    def __init__(
        self,
        gdb_path: str,
        gdb_port: int = 3333,
        remote_host: str = "localhost",
        elf_file: str = None,
        startup_delay=0.1,
    ):
        self.remote_host = remote_host
        self.gdb_port = gdb_port
        self.gdb_path = gdb_path
        gdb_command = [
            gdb_path,
            "--interpreter=mi",
            "-ex",
            f"target remote {remote_host}:{gdb_port}",
        ]
        if elf_file:
            gdb_command.append(elf_file)

        self.gdb_process = Popen(gdb_command, stdin=PIPE, stdout=PIPE, stderr=PIPE, bufsize=0)

        time.sleep(startup_delay)

        # Flush the output from GDB
        self.dump_output()

        # Start clean
        self.send_command("delete breakpoints", timeout=5)

        # Set number of breakpoints
        self.n_brkp = 1

    def read_output(self, timeout: float = 0.5) -> str:
        if not self.gdb_process:
            return ""

        output = ""

        readable_pipes = []
        if self.gdb_process.stdout:
            readable_pipes.append(self.gdb_process.stdout.fileno())
        if self.gdb_process.stderr:
            readable_pipes.append(self.gdb_process.stderr.fileno())

        try:
            readable, _, _ = select.select(readable_pipes, [], [], timeout)

            for fd in readable:
                if fd == self.gdb_process.stdout.fileno():
                    data = os.read(fd, 4096).decode("utf-8", errors="ignore")
                    output += data
                elif fd == self.gdb_process.stderr.fileno():
                    # GDB MI uses stderr mostly for logging/errors
                    err_data = os.read(fd, 4096).decode("utf-8", errors="ignore")
                    print(f"GDB-MI Stderr: {err_data}", flush=True)
        except Exception as e:
            print(f"Error reading GDB output: {e}", flush=True)

        return output

    def dump_output(self, timeout: float = 0.5) -> str:
        self.read_output(timeout=timeout)

    def send_command(self, mi_command: str, timeout: float = 2.0, check_response=True) -> str:
        if not self.gdb_process or not self.gdb_process.stdin:
            raise RuntimeError("GDB process not started or stdin not available.")

        command_line = mi_command.strip() + "\n"

        self.gdb_process.stdin.write(command_line.encode("utf-8"))
        self.gdb_process.stdin.flush()

        if check_response:
            start_time = time.time()
            response = ""
            while True:
                response += self.read_output(timeout=0.1)

                if response.strip().endswith("(gdb)") or (
                    "^done" in response and response.strip().endswith("=")
                ):
                    break

                if time.time() - start_time > timeout:
                    raise TimeoutError(
                        f"GDB timed out after {timeout}s. Current output: {response}, {mi_command}"
                    )

            # To debug you can print this output to see GDB's response
            return response
        else:
            return None

    def reset_target(self, reset_delay=0.005):
        self.send_command("monitor reset run", check_response=False)
        self.dump_output()
        time.sleep(reset_delay)

    def close_gdb(self):
        # Note that closing OpenOCD also closes GDB
        self.dump_output()
        if self.gdb_process:
            if self.gdb_process.poll() is None:
                try:
                    self.gdb_process.send_signal(signal.SIGINT)
                    self.gdb_process.wait(timeout=0.3)
                except TimeoutExpired:
                    self.gdb_process.kill()
                    self.gdb_process.wait()
            self.gdb_process = None

    def get_program_counter(self) -> Optional[str]:
        mi_command = "-data-evaluate-expression $pc"
        response = self.send_command(mi_command)

        try:
            import re

            match = re.search(r'value="([^"]+)"', response)
            if match:
                return match.group(1).strip()

            if "^error" in response:
                raise RuntimeError(f"GDB returned an error: {response}")

        except Exception as e:
            print(
                f"Error parsing GDB response: {e}\nFull Response: {response}",
                flush=True,
            )
            return None

    def setup_pc_trace(self, file_name: str, trace_start_addr: str, trace_end_addr: str):
        self.send_command("delete breakpoints")
        self.n_brkp = 1
        self.send_command(f"set logging file {file_name}")
        self.send_command("set logging overwrite on")
        self.send_command("set pagination off")
        self.send_command("set logging enabled on")
        traceloop_definition = f"""\
        define traceloop
            while 1
                if $pc=={trace_end_addr}
                    printf "PC trace complete.\\n"
                    return
                end
                printf "PC: 0x%x\\n", $pc
                stepi
            end
        end
        """
        self.send_command(traceloop_definition)
        self.send_command(f"hbreak *({trace_start_addr})")
        commands_definition = "commands 1\ntraceloop\nend"
        self.send_command(commands_definition)
        self.n_brkp += 1

    def parse_pc_trace_file(self, file_path):
        pc_list = []
        # Regex to find 'PC: 0x' followed by one or more hex characters
        pc_pattern = re.compile(r"PC: (0x[0-9a-fA-F]+)")

        try:
            with open(file_path, "r") as f:
                for line in f:
                    match = pc_pattern.search(line)
                    if match:
                        # Append the full hex string (e.g., '0x200265a2')
                        pc_list.append(match.group(1))
        except FileNotFoundError:
            print(f"Error: Trace file not found at {file_path}", flush=True)
        except Exception as e:
            print(f"Error reading or parsing trace file: {e}", flush=True)

        return pc_list

    def get_function_addresses(self, file_path, function_name):
        if not os.path.exists(file_path):
            print(f"Error: File not found at path: {file_path}")
            return []

        try:
            with open(file_path, "r") as f:
                dis_content = f.read()
        except IOError as e:
            print(f"Error reading file: {e}")
            return []

        addresses = []
        escaped_name = re.escape(function_name)
        lines = dis_content.splitlines()

        jump_line_pattern = re.compile(r"^\s*([0-9a-fA-F]{8}):.*?<" + escaped_name + r">")

        next_addr_pattern = re.compile(r"^\s*([0-9a-fA-F]{8}):")

        for i, line in enumerate(lines):
            match = jump_line_pattern.match(line)
            if match:
                jump_address = match.group(1)

                for j in range(i + 1, len(lines)):
                    next_line = lines[j]

                    if not next_line.strip():
                        continue

                    next_match = next_addr_pattern.match(next_line)

                    if next_match:
                        address_after_jump = next_match.group(1)
                        addresses.append((f"0x{jump_address}", f"0x{address_after_jump}"))
                        break

        return addresses

    def parse_next_instruction(self, pc_address, dis_path):
        if not os.path.exists(dis_path):
            print(f"Error: File not found at path: {dis_path}")
            return None

        if pc_address.startswith("0x"):
            pc_address = pc_address[2:]

        instruction_addr_pattern = re.compile(r"^\s*([0-9a-fA-F]{8}):")

        found_current_address = False

        try:
            with open(dis_path, "r") as f:
                for line in f:
                    match = instruction_addr_pattern.match(line)

                    if match:
                        line_address = match.group(1)

                        if not found_current_address:
                            if line_address == pc_address:
                                found_current_address = True
                        else:
                            return f"0x{line_address}"

                if found_current_address:
                    return None
                else:
                    print(f"Error: Address 0x{pc_address} not found in disassembly.")
                    return None

        except IOError as e:
            print(f"Error reading file: {e}")
            return None

    def get_function_start_address(self, dis_path, function_name):
        try:
            with open(dis_path, "r") as f:
                for line in f:
                    escaped_name = re.escape(function_name)
                    pattern = re.compile(r"^([0-9a-fA-F]{8})\s*<" + escaped_name + r">:")

                    match = pattern.search(line)
                    if match:
                        return f"0x{match.group(1)}"

        except IOError as e:
            print(f"Error reading file: {e}")
            return None

        return None

    def apply_instruction_skip(self, pc_address, next_pc_address):
        skip_commands = (
            f"commands {self.n_brkp}\n"
            f"set $pc={next_pc_address}\n"
            'printf "instruction skip applied\\n"\n'
            "c\n"
            "end"
        )

        self.send_command(f"hbreak *({pc_address})")
        self.send_command(skip_commands)
        self.n_brkp += 1

    def add_observation(self, observations):
        for addr, log_message in observations.items():
            obs_command = f"commands {self.n_brkp}\n"
            obs_command += f'printf "fisim_result: {log_message} \\n"\n'
            obs_command += "c\n"
            obs_command += "end"

            self.send_command(f"tb *({addr})")
            self.send_command(obs_command)
            self.n_brkp += 1
