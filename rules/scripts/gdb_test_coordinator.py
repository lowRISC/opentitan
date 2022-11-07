# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""This script runs a GDB test and coordinates the required processes.

It loads a bitstream onto the connected FPGA and then launches OpenOCD, GDB, and
`opentitantool console` in the background. If any of these background processes
exit unsuccessfully, this script will exit with the same status. The one
exception is that we expect to terminate OpenOCD, which may cause it to exit
with a non-zero status.

Note that it is tightly coupled to the `opentitan_gdb_fpga_cw310_test` rule.
"""

import selectors
import subprocess
import sys
from typing import Dict, List, NewType, Optional, TextIO, Tuple

import rich
import typer

ConsoleStyle = NewType('ConsoleStyle', str)
COLOR_RED = ConsoleStyle('red')
COLOR_GREEN = ConsoleStyle('green')
COLOR_PURPLE = ConsoleStyle('purple')


class BackgroundProcessGroup:

    def __init__(self):
        self.selector = selectors.DefaultSelector()
        self.procs_queue: List[subprocess.Popen] = []
        self.names: Dict[subprocess.Popen, str] = {}
        self.console = rich.console.Console(color_system="256")

    def run(self, command: List[str], label: str,
            style: ConsoleStyle) -> subprocess.Popen:
        proc = subprocess.Popen(command,
                                stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT,
                                encoding='utf-8')
        self.procs_queue.append(proc)
        self.names[proc] = label

        # Register the new process with our selector. The `echo` closure may be
        # called multiple times by `maybe_print_output`.
        def echo(line):
            self.console.print(f"[{label}] ", style=style, end='')
            print(line, flush=True)

        self.selector.register(proc.stdout, selectors.EVENT_READ, echo)
        return proc

    def empty(self) -> bool:
        return len(self.procs_queue) == 0

    def pop(self) -> subprocess.Popen:
        return self.procs_queue.pop(0)

    def push(self, proc: subprocess.Popen) -> None:
        return self.procs_queue.append(proc)

    def get_name(self, proc: subprocess.Popen) -> str:
        return self.names[proc]

    def forget(self, proc: subprocess.Popen) -> None:
        assert proc not in self.procs_queue
        self.maybe_print_output(
            timeout_seconds=1)  # Flush any remaining lines.
        self.selector.unregister(proc.stdout)
        self.names.pop(proc, None)

    def _block_for_output(self,
                          timeout_seconds: int) -> List[Tuple[TextIO, str]]:
        out = []
        events = self.selector.select(timeout=timeout_seconds)
        for key, mask in events:
            line = key.fileobj.readline().rstrip()
            callback = key.data
            callback(line)
            out.append((key.fileobj, line))
        return out

    def maybe_print_output(self, timeout_seconds: int) -> None:
        self._block_for_output(timeout_seconds)

    def block_until_line_contains(self, proc: subprocess.Popen,
                                  output_fragment: str) -> None:
        while True:
            for fileobj, line in self._block_for_output(1):
                if fileobj == proc.stdout and output_fragment in line:
                    return


app = typer.Typer(pretty_exceptions_enable=False)


@app.command()
def main(rom_kind: str = typer.Option(...),
         openocd_path: str = typer.Option(...),
         openocd_earlgrey_config: str = typer.Option(...),
         openocd_jtag_adapter_config: str = typer.Option(...),
         gdb_path: str = typer.Option(...),
         gdb_script_path: str = typer.Option(...),
         bitstream_path: str = typer.Option(...),
         opentitantool_path: str = typer.Option(...),
         exit_success_pattern: Optional[str] = typer.Option(None)):

    opentitantool_prefix = [
        opentitantool_path,
        "--rcfile=",
        "--logging=info",
        "--interface=cw310",
    ]
    load_bitstream_command = opentitantool_prefix + [
        "fpga",
        "load-bitstream",
        "--rom-kind=" + rom_kind,
        bitstream_path,
    ]
    openocd_command = [
        openocd_path,
        "-f",
        openocd_jtag_adapter_config,
        "-c",
        "adapter speed 0; transport select jtag; reset_config trst_and_srst",
        "-f",
        openocd_earlgrey_config,
    ]
    gdb_command = [
        # For debugging, it may be useful to use `--init-command`, which causes
        # GDB to drop to the interactive prompt when the script ends rather than
        # exit.
        gdb_path,
        "--batch",
        "--command=" + gdb_script_path,
    ]
    console_command = opentitantool_prefix + [
        "console",
        "--timeout",
        "5s",
    ]
    if exit_success_pattern is not None:
        console_command.append("--exit-success=" + exit_success_pattern)

    # Wait until we've finished loading the bitstream.
    subprocess.run(load_bitstream_command, check=True)

    # Run OpenOCD, GDB, and the OpenTitanTool console in the background. Wait
    # until OpenOCD has fired up its GDB server before launching the GDB client
    # to avoid a subtle race condition.
    background = BackgroundProcessGroup()
    openocd = background.run(openocd_command, "OPENOCD", COLOR_PURPLE)
    # For some reason, we don't reliably see the "starting gdb server" line when
    # OpenOCD's GDB server is ready. It could be a buffering issue internal to
    # OpenOCD or perhaps this script.
    background.block_until_line_contains(
        openocd, "Examined RISC-V core; found 1 harts")

    background.run(gdb_command, "GDB", COLOR_GREEN)
    background.run(console_command, "CONSOLE", COLOR_RED)

    while not background.empty():
        background.maybe_print_output(timeout_seconds=1)

        proc = background.pop()

        # When OpenOCD is the only remaining process, send it the TERM signal
        # and wait for it to exit. GDB will exit naturally at the end of its
        # script. The opentitantool console will either time out or exit due to
        # the given success pattern.
        if background.empty() and proc == openocd:
            openocd.terminate()
            openocd.wait()
            background.forget(openocd)
            break

        returncode = proc.poll()
        if returncode is None:  # (If the process is still running...)
            background.push(proc)
            continue

        print(f"{background.get_name(proc)} exited with code {returncode}")

        if returncode != 0:
            sys.exit(returncode)

        background.forget(proc)


if __name__ == '__main__':
    app()
