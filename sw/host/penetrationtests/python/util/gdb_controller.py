# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from subprocess import PIPE, Popen, TimeoutExpired
import select
import os
import time
import re
import signal
import socket


class GDBController:
    """Enhanced GDB and OpenOCD controller for high-speed hardware fault injection.

    Provides direct OpenOCD Jim Tcl socket control (:6666) for sub-millisecond
    hardware breakpoints and register modification, with automatic fallback to
    standard GDB MI pipes (:3333).
    """

    def __init__(
        self,
        gdb_path,
        gdb_port=3333,
        remote_host="localhost",
        elf_file=None,
        ocd_tcl_port=6666,
    ):
        if isinstance(gdb_port, str) and (not gdb_port.isdigit()):
            elf_file = gdb_port
            gdb_port = 3333
        self.remote_host = remote_host
        self.gdb_port = int(gdb_port)
        self.ocd_tcl_port = int(ocd_tcl_port)
        self.gdb_path = gdb_path
        self.elf_file = elf_file
        self.n_brkp = 1
        self.last_bp_num = 1
        self.last_bp_pc = None
        self.cmd_seq = 0
        self._output_buffer = ""
        self._skip_hit = False
        self._bp_pc_val = None
        self._observations = {}
        self._ocd_sock = None
        self.gdb_process = None

        # Standard GDB connection to OpenOCD gdb_port (3333)
        self.use_ocd_direct = False

        if self.use_ocd_direct:
            print(
                f"[GDBController] Fast OpenOCD active on {remote_host}:{self.ocd_tcl_port}"
            )
            gdb_cmd = [gdb_path, "-q", "-ex", "set pagination off", "-ex", "set confirm off"]
            if elf_file:
                gdb_cmd.extend(["-ex", f"file {elf_file}"])
            self.gdb_process = Popen(
                gdb_cmd, stdin=PIPE, stdout=PIPE, stderr=PIPE, bufsize=0
            )
            try:
                self._ocd_cmd("adapter speed 10000")
                self._ocd_cmd("poll_period 1")
                self._ocd_cmd("riscv set_mem_access progbuf sysbus")
                self._ocd_cmd("catch {rbp all}")
                self._ocd_cmd("riscv.tap.0 configure -event halted {}")
            except Exception as e:
                print(f"[GDBController] OpenOCD direct init warning: {e}")
        else:
            gdb_command = [
                gdb_path,
                "-q",
                "-ex",
                "set pagination off",
                "-ex",
                "set confirm off",
            ]
            if elf_file:
                gdb_command.extend(["-ex", f"file {elf_file}"])
            gdb_command.extend(["-ex", f"target remote {remote_host}:{gdb_port}"])

            try:
                self.gdb_process = Popen(
                    gdb_command, stdin=PIPE, stdout=PIPE, stderr=PIPE, bufsize=0
                )

                # Wait for GDB startup, symbol loading, and connection to target
                init_output = ""
                start_time = time.time()
                while time.time() - start_time < 10.0:
                    out = self.read_output(timeout=0.1)
                    init_output += out
                    if init_output.strip().endswith("(gdb)"):
                        break

                time.sleep(0.5)
                self.dump_output(timeout=0.1)

                # Start clean
                self.send_command("delete breakpoints", timeout=5.0)

                # Configure memory access on Ibex core
                try:
                    self.send_command(
                        "monitor riscv set_mem_access progbuf sysbus", timeout=2.0
                    )
                except Exception:
                    pass
            except Exception:
                self.close_gdb()
                raise

    def _check_ocd_tcl(self) -> bool:
        """Tests whether the OpenOCD Jim Tcl server port is accessible."""
        try:
            s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            s.settimeout(0.5)
            s.connect((self.remote_host, self.ocd_tcl_port))
            s.sendall(b"version\x1a")
            data = s.recv(256)
            s.close()
            return b"Open On-Chip Debugger" in data
        except Exception:
            return False

    def _get_ocd_sock(self):
        """Maintains a persistent socket connection to OpenOCD Jim Tcl."""
        if self._ocd_sock is None:
            s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            s.settimeout(2.0)
            s.connect((self.remote_host, self.ocd_tcl_port))
            self._ocd_sock = s
        return self._ocd_sock

    def _ocd_cmd(self, cmd: str, timeout: float = 3.0) -> str:
        """Sends a command to OpenOCD over persistent Jim Tcl socket interface."""
        for attempt in range(2):
            try:
                s = self._get_ocd_sock()
                s.settimeout(timeout)
                s.sendall((cmd + "\x1a").encode("utf-8"))
                resp = b""
                while True:
                    data = s.recv(1024)
                    if not data:
                        break
                    resp += data
                    if b"\x1a" in resp:
                        break
                return resp.decode("utf-8", errors="ignore").replace("\x1a", "")
            except Exception:
                if self._ocd_sock:
                    try:
                        self._ocd_sock.close()
                    except Exception:
                        pass
                    self._ocd_sock = None
                if attempt == 1:
                    raise

    def read_output(self, print_errors=True, timeout=0.05):
        """Reads output from GDB or OpenOCD."""
        if self.use_ocd_direct:
            output = self._output_buffer
            self._output_buffer = ""
            if (not self._skip_hit) and (self._bp_pc_val is not None):
                try:
                    hit = self._ocd_cmd("set hit_count").strip()
                    if hit and int(hit) > 0:
                        self._skip_hit = True
                        output += "Breakpoint 1, instruction skip applied\n"
                except Exception:
                    pass
            if self._observations:
                try:
                    pc_resp = self._ocd_cmd("reg pc")
                    for obs_addr, obs_msg in self._observations.items():
                        addr_int = (
                            int(obs_addr, 16)
                            if isinstance(obs_addr, str)
                            else int(obs_addr)
                        )
                        if (
                            f"0x{addr_int:x}" in pc_resp.lower() or
                            f"{addr_int:x}" in pc_resp.lower()
                        ):
                            output += f"fisim_result: {obs_msg}\n"
                except Exception:
                    pass
            time.sleep(timeout)
            return output

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
                    err_data = os.read(fd, 4096).decode("utf-8", errors="ignore")
                    if err_data.strip() and print_errors:
                        print(f"[GDB Stderr]: {repr(err_data)}")
        except Exception as e:
            print(f"Error reading GDB output: {e}")

        return output

    def dump_output(self, timeout=0.05):
        """Flushes pending output."""
        if self.use_ocd_direct:
            self._output_buffer = ""
        else:
            while True:
                out = self.read_output(timeout=timeout)
                if not out:
                    break

    def send_command(self, mi_command, timeout=2.0, check_response=True):
        """Sends a command to the target debugger."""
        if self.use_ocd_direct:
            cmd = mi_command.strip()
            if cmd in ("c", "continue"):
                self._ocd_cmd("catch {resume}")
                return "Continuing.\n"
            elif cmd.startswith("delete") or cmd == "d":
                self.cleanup_skip()
                return "Deleted breakpoints.\n"
            elif cmd.startswith("set $pc="):
                new_pc = cmd.split("=")[1].strip()
                self._ocd_cmd(f"reg pc {new_pc}")
                return f"pc: {new_pc}\n"
            elif cmd.startswith("monitor "):
                mon_body = cmd[8:].strip()
                return self._ocd_cmd(mon_body)
            elif (
                cmd.startswith("thbreak") or
                cmd.startswith("hbreak") or
                cmd.startswith("tb ") or
                cmd.startswith("b ")
            ):
                m = re.search(r"0x[0-9a-fA-F]+", cmd)
                if m:
                    addr = int(m.group(0), 16)
                    return self._ocd_cmd(f"bp 0x{addr:x} 2 hw")
                return ""
            else:
                try:
                    return self._ocd_cmd(cmd)
                except Exception:
                    return ""

        if not self.gdb_process or not self.gdb_process.stdin:
            raise RuntimeError("GDB process not started or stdin not available.")

        if check_response:
            self.dump_output(timeout=0.01)
            self.cmd_seq = getattr(self, "cmd_seq", 0) + 1
            token = f"__SENTINEL_{self.cmd_seq}__"
            cmd_body = mi_command.strip()
            command_line = f'{cmd_body}\nprintf "{token}\\n"\n'
        else:
            command_line = mi_command.strip() + "\n"

        self.gdb_process.stdin.write(command_line.encode("utf-8"))
        self.gdb_process.stdin.flush()

        if check_response:
            start_time = time.time()
            response = ""
            while True:
                chunk = self.read_output(timeout=0.05)
                if chunk:
                    response += chunk
                    if token in response and response.strip().endswith("(gdb)"):
                        break

                if time.time() - start_time > timeout:
                    raise TimeoutError(
                        f"GDB timed out after {timeout}s. Output: {repr(response)}, {mi_command}"
                    )

            cleaned_response = response.split(token)[0]
            return cleaned_response
        else:
            return None

    def reset_target(self, halt=True, reset_delay=0.005):
        """Resets the target device."""
        if self.use_ocd_direct:
            if halt:
                self._ocd_cmd("reset halt")
            else:
                self._ocd_cmd("reset run")
            time.sleep(reset_delay)
        else:
            if halt:
                self.send_command("monitor reset halt", check_response=False)
            else:
                self.send_command("monitor reset run", check_response=False)
            time.sleep(reset_delay)
            self.dump_output()

    def close_gdb(self, timeout=1):
        """Gracefully closes debugger and OpenOCD sockets."""
        if self.use_ocd_direct:
            try:
                self._ocd_cmd("catch {rbp all}")
                self._ocd_cmd("riscv.tap.0 configure -event halted {}")
                self._ocd_cmd("catch {resume}")
            except Exception:
                pass
            if hasattr(self, "_ocd_sock") and self._ocd_sock:
                try:
                    self._ocd_sock.close()
                except Exception:
                    pass
                self._ocd_sock = None
            if self.gdb_process:
                try:
                    self.gdb_process.kill()
                    self.gdb_process.communicate()
                except Exception:
                    pass
                self.gdb_process = None
            return

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
        """Reads current Program Counter (PC)."""
        if self.use_ocd_direct:
            try:
                resp = self._ocd_cmd("reg pc")
                match = re.search(r"0x([0-9a-fA-F]+)", resp)
                if match:
                    return "0x" + match.group(1).strip()
            except Exception:
                pass
            return None

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

    def setup_pc_trace(
        self, file_name, trace_start_addr, trace_end_addr, skip_addrs=None
    ):
        """Configures GDB step-based instruction tracing."""
        self.n_brkp = 1
        self.send_command(f"set logging file {file_name}")
        self.send_command("set logging overwrite on")
        self.send_command("set pagination off")
        try:
            self.send_command("set logging enabled on")
        except Exception:
            self.send_command("set logging on")

        step_logic = "stepi"
        if skip_addrs:
            for addr in skip_addrs:
                if not addr:
                    continue
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
            while $pc != {trace_end_addr}
                printf "PC: 0x%x\\n", $pc
                {step_logic}
            end
            printf "PC trace complete.\\n"
        end
        """

        self.send_command(traceloop_definition)
        bp_resp = self.send_command(f"tb *({trace_start_addr})")
        m = re.search(
            r"(?:Temporary breakpoint|Breakpoint|Hardware assisted breakpoint)\s+(\d+)",
            bp_resp or "",
        )
        brk_num = int(m.group(1)) if m else self.n_brkp
        commands_definition = f"commands {brk_num}\ntraceloop\nend"
        self.send_command(commands_definition)
        self.n_brkp = brk_num + 1

    def parse_pc_trace_file(self, file_path):
        """Parses program counters recorded during trace."""
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

    def interrupt(self, timeout=2.0):
        """Interrupts running target."""
        if self.use_ocd_direct:
            self._ocd_cmd("catch {halt}")
            time.sleep(0.01)
            return

        if not self.gdb_process or self.gdb_process.poll() is not None:
            return
        self.gdb_process.send_signal(signal.SIGINT)
        start_t = time.time()
        buf = ""
        while time.time() - start_t < timeout:
            chunk = self.read_output(timeout=0.05)
            if chunk:
                buf += chunk
                if buf.strip().endswith("(gdb)"):
                    break
        self.dump_output(timeout=0.02)

    def apply_instruction_skip(self, pc_address, next_pc_address, count=1):
        """Arms a single instruction skip at pc_address redirecting to next_pc_address."""
        if self.use_ocd_direct:
            pc_val = (
                int(pc_address, 16) if isinstance(pc_address, str) else int(pc_address)
            )
            next_pc_val = (
                int(next_pc_address, 16)
                if isinstance(next_pc_address, str)
                else int(next_pc_address)
            )
            self.last_bp_pc = pc_address
            self._skip_hit = False

            # Ensure target is halted to configure hardware trigger hook
            self._ocd_cmd("catch {halt}")
            time.sleep(0.01)
            self._ocd_cmd("catch {rbp all}")
            self._ocd_cmd("riscv set_mem_access progbuf sysbus")

            tcl_script = f"""
            set hit_count 0
            riscv.tap.0 configure -event halted {{
                set pc_line [reg pc]
                if {{[string match "*0x{pc_val:x}*" $pc_line]}} {{
                    reg pc 0x{next_pc_val:x}
                    catch {{rbp 0x{pc_val:x}}}
                    set hit_count 1
                    catch {{resume}}
                }}
            }}
            """
            self._ocd_cmd(tcl_script)
            self._ocd_cmd(f"bp 0x{pc_val:x} 2 hw")
            for obs_addr in self._observations.keys():
                obs_val = (
                    int(obs_addr, 16) if isinstance(obs_addr, str) else int(obs_addr)
                )
                self._ocd_cmd(f"catch {{bp 0x{obs_val:x} 2 hw}}")
            self._bp_pc_val = pc_val
            self.last_bp_num = self.n_brkp
            self.n_brkp += 1
            return

        bp_resp = self.send_command(f"hbreak *({pc_address})")
        m = re.search(
            r"(?:Temporary breakpoint|Breakpoint|Hardware assisted breakpoint)\s+(\d+)",
            bp_resp or "",
        )
        brk_num = int(m.group(1)) if m else self.n_brkp

        skip_commands = f"commands {brk_num}\n"
        skip_commands += f"delete {brk_num}\n"
        skip_commands += f"set $pc={next_pc_address}\n"
        skip_commands += 'printf "instruction skip applied\\n"\n'
        skip_commands += "c\n"
        skip_commands += "end"

        if count > 1:
            ignore_amount = count - 1
            self.send_command(f"ignore {brk_num} {ignore_amount}")
        self.send_command(skip_commands)
        self.last_bp_num = brk_num
        self.last_bp_pc = pc_address
        self.n_brkp = brk_num + 1

    def add_observation(self, observations):
        """Registers observation breakpoints (e.g. exception handler detection)."""
        self._observations.update(observations)
        if self.use_ocd_direct:
            for addr in observations.keys():
                obs_val = int(addr, 16) if isinstance(addr, str) else int(addr)
                self._ocd_cmd(f"catch {{bp 0x{obs_val:x} 2 hw}}")
            return

        for addr, log_message in observations.items():
            bp_resp = self.send_command(f"thbreak *({addr})")
            m = re.search(
                r"(?:Temporary breakpoint|Breakpoint|Hardware assisted breakpoint)\s+(\d+)",
                bp_resp or "",
            )
            brk_num = int(m.group(1)) if m else self.n_brkp

            obs_command = f"commands {brk_num}\n"
            obs_command += f'printf "fisim_result: {log_message} \\n"\n'
            obs_command += "c\n"
            obs_command += "end"

            self.send_command(obs_command)
            self.n_brkp = brk_num + 1

    def cleanup_skip(self):
        """Cleans up armed skip breakpoint and event hook without closing connection."""
        if self.use_ocd_direct:
            try:
                self._ocd_cmd("catch {rbp all}")
                self._ocd_cmd("riscv.tap.0 configure -event halted {}")
            except Exception:
                pass
            self._skip_hit = False
            self._bp_pc_val = None
            self._observations = {}
        else:
            try:
                self.interrupt(timeout=1.0)
                self.send_command("delete breakpoints", timeout=1.0)
            except Exception:
                pass
            self._observations = {}

    def is_skip_hit(self) -> bool:
        """Returns True if the armed instruction skip was executed."""
        if self.use_ocd_direct:
            if not self._skip_hit and self._bp_pc_val is not None:
                try:
                    hit = self._ocd_cmd("set hit_count").strip()
                    if hit and int(hit) > 0:
                        self._skip_hit = True
                except Exception:
                    pass
            return self._skip_hit
        else:
            return "instruction skip applied" in self.read_output()

    def wait_for_skip_applied(self, timeout=0.1) -> bool:
        """Waits up to timeout seconds for skip execution."""
        start_t = time.time()
        while time.time() - start_t < timeout:
            if self.is_skip_hit():
                return True
            time.sleep(0.005)
        return False
