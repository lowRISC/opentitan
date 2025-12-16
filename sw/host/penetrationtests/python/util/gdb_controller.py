# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from subprocess import PIPE, Popen, TimeoutExpired
import select
import os
import time
import re
import signal


class GDBController:
    def __init__(self, gdb_path, gdb_port=3333, remote_host="localhost", elf_file=None):
        self.remote_host = remote_host
        self.gdb_port = gdb_port
        self.gdb_path = gdb_path
        gdb_command = [
            gdb_path,
            "-ex",
            f"target remote {remote_host}:{gdb_port}",
        ]
        if elf_file:
            gdb_command.append(elf_file)

        try:
            self.gdb_process = Popen(gdb_command, stdin=PIPE, stdout=PIPE, stderr=PIPE, bufsize=0)

            # Flush the output from GDB
            self.dump_output()
            # Start clean
            self.send_command("delete breakpoints", timeout=10)
            # Need to flush again from the breakpoints
            self.dump_output()

            # Set number of breakpoints
            self.n_brkp = 1
        except Exception:
            self.close_gdb()
            raise

    def read_output(self, print_errors=False, timeout=0.05):
        if not self.gdb_process:
            return ""

        output = ""
        readable_pipes = []
        if self.gdb_process.stdout:
            readable_pipes.append(self.gdb_process.stdout.fileno())
        if self.gdb_process.stderr:
            readable_pipes.append(self.gdb_process.stderr.fileno())

        while True:
            try:
                current_timeout = timeout if output == "" else 0
                readable, _, _ = select.select(readable_pipes, [], [], current_timeout)

                if not readable:
                    break

                data_read = False
                for fd in readable:
                    if fd == self.gdb_process.stdout.fileno():
                        chunk = os.read(fd, 4096).decode("utf-8", errors="ignore")
                        if chunk:
                            output += chunk
                            data_read = True
                    elif fd == self.gdb_process.stderr.fileno():
                        err_chunk = os.read(fd, 4096).decode("utf-8", errors="ignore")
                        if err_chunk:
                            if print_errors:
                                print(f"GDB Stderr: {err_chunk}")
                            data_read = True

                if not data_read:
                    break

            except Exception as e:
                print(f"Error reading GDB output: {e}")
                break

        return output

    def dump_output(self, timeout=0.05):
        self.read_output(timeout=timeout)

    def send_command(self, mi_command, timeout=0.05, check_response=True):
        if not self.gdb_process or not self.gdb_process.stdin:
            raise RuntimeError("GDB process not started or stdin not available.")

        command_line = mi_command.strip() + "\n"

        self.gdb_process.stdin.write(command_line.encode("utf-8"))
        # After sending the command let's wait for a while till the command is
        # processed on the receiving end
        time.sleep(0.1)

        self.gdb_process.stdin.flush()

        if check_response:
            start_time = time.time()
            response = ""
            while True:
                response += self.read_output()

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

    def reset_target(self, halt=True, reset_delay=0.005):
        if halt:
            self.send_command("monitor reset halt", check_response=False)
        else:
            self.send_command("monitor reset run", check_response=False)
        time.sleep(reset_delay)
        self.dump_output()

    def close_gdb(self, timeout=1):
        if not self.gdb_process or self.gdb_process.poll() is not None:
            return

        self.dump_output()
        self.gdb_process.send_signal(signal.SIGINT)
        try:
            self.gdb_process.communicate(timeout=timeout)
        except TimeoutExpired:
            self.gdb_process.kill()
            self.gdb_process.communicate()
        finally:
            self.gdb_process = None

    def get_program_counter(self):
        gdb_command = "p $pc"

        try:
            response = self.send_command(gdb_command, timeout=0.5)
            pc_pattern = re.compile(r"0x([0-9a-fA-F]+)")
            match = pc_pattern.search(response)
            if match:
                return "0x" + match.group(1).strip()
            if "No symbol " in response or "Undefined command" in response:
                raise RuntimeError(f"GDB returned an error: {response}")

        except Exception:
            return None

    def setup_pc_trace(self, file_name, trace_start_addr, trace_end_addr, skip_addrs=None):
        self.n_brkp = 1
        self.send_command(f"set logging file {file_name}")
        self.send_command("set logging overwrite on")
        self.send_command("set pagination off")
        self.send_command("set logging on")

        step_logic = "stepi"
        if skip_addrs:
            for addr in skip_addrs:
                step_logic = f"""
                if $pc == {addr}
                    tbreak *$ra
                    c
                else
                    {step_logic}
                end
                """

        traceloop_definition = f"""\
        define traceloop
            while 1
                if $pc=={trace_end_addr}
                    printf "PC trace complete.\\n"
                    return
                end
                printf "PC: 0x%x\\n", $pc
                {step_logic}
            end
        end
        """

        self.send_command(traceloop_definition)
        self.send_command(f"tb *({trace_start_addr})")
        commands_definition = "commands 1\ntraceloop\nend"
        self.send_command(commands_definition)
        self.n_brkp += 1

    def parse_pc_trace_file(self, file_path):
        pc_list = []
        pc_pattern = re.compile(r"PC: (0x[0-9a-fA-F]+)")

        try:
            with open(file_path, "r") as f:
                for line in f:
                    match = pc_pattern.search(line)
                    if match:
                        pc_list.append(match.group(1))
        except FileNotFoundError:
            print(f"Error: Trace file not found at {file_path}")
        except Exception as e:
            print(f"Error reading or parsing trace file: {e}")

        return pc_list

    def apply_instruction_skip(self, pc_address, next_pc_address, count):
        skip_commands = f"commands {self.n_brkp}\n"
        skip_commands += f"set $pc={next_pc_address}\n"
        skip_commands += 'printf "instruction skip applied\\n"\n'
        skip_commands += "c\n"
        skip_commands += "end"

        self.send_command(f"tb *({pc_address})")
        if count > 1:
            ignore_amount = count - 1
            self.send_command(f"ignore {self.n_brkp} {ignore_amount}")
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
