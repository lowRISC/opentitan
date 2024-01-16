#!/usr/bin/env python3
import argparse
import subprocess
import os
import tempfile

# =============================================================================

REPL_TEMPLATE = """
memory: Memory.MappedMemory @ sysbus 0x80000000
    size: 0x10000

cpu: CPU.RiscV32 @ sysbus
    cpuType: "{isa}"
    timeProvider: clint
    hartId: 0

clint: IRQControllers.CoreLevelInterruptor  @ sysbus 0x02000000
    [0,1] -> cpu@[3,7]
    frequency: 1000000
"""

RESC_TEMPLATE = """
using sysbus
mach create "riscv"
machine LoadPlatformDescription @{repl}

sysbus LoadELF @{elf}

cpu MaximumBlockSize 1
cpu SetHookAtBlockEnd "print('REGDUMP:' + ','.join(self.GetRegistersValues()))"

emulation RunFor "0.000100"

quit
"""

# =============================================================================


def main():
    """
    The entry point
    """

    parser = argparse.ArgumentParser()

    parser.add_argument(
        "--renode",
        type=str,
        default="renode",
        help="Path to Renode binary",
    )
    parser.add_argument(
        "--log",
        type=str,
        default=None,
        help="Output log file",
    )
    parser.add_argument(
        "--isa",
        type=str,
        default="rv32i",
        help="RISC-V ISA specification string",
    )
    parser.add_argument(
        "--elf",
        type=str,
        required=True,
        help="ELF file to run",
    )

    args = parser.parse_args()

    with tempfile.TemporaryDirectory() as tmpdir:

        repl = os.path.join(tmpdir, "riscv.repl")
        resc = os.path.join(tmpdir, "riscv.resc")

        params = {
            "renode": args.renode,
            "isa":  args.isa,
            "elf":  args.elf,
            "repl": repl,
            "resc": resc,
            "log":  args.log,
        }

        # Render REPL template
        with open(repl, "w") as fp:
            fp.write(REPL_TEMPLATE.format(**params))

        # Render RESC template
        with open(resc, "w") as fp:
            fp.write(RESC_TEMPLATE.format(**params))

        # Launch Renode, capture output
        cmd = "{renode} --console -p {resc}".format(**params)
        if args.log is not None:
            cmd += " &>{log}".format(**params)

        subprocess.call(cmd, shell=True)


if __name__ == "__main__":
    main()
