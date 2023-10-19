#!/usr/bin/env python3
import argparse
import re

# =============================================================================

class AssemblyLine:
    """
    Simple assembly line representation
    """

    RE_INSTR = re.compile(r"(?P<mnemonic>\S+)\s+(?P<operands>.*)")

    def __init__(self, text):
        self.text       = text
        self.mnemonic   = None
        self.operands   = None

        # Strip label if any
        if ":" in text:
            text = text.split(":", maxsplit=1)[1]

        # Strip comment if any
        if "#" in text:
            text = text.split("#", maxsplit=1)[0]

        # Get instruction and operands
        m = self.RE_INSTR.match(text.strip())
        if m is not None:

            if m.group("mnemonic")[0] == ".":
                return

            self.mnemonic = m.group("mnemonic").lower()
            self.operands = [op.strip() for op in m.group("operands").split()]

    def __str__(self):
        return self.text

# =============================================================================


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "-i",
        type=str,
        required=True,
        help="Input assembly file"
    )
    parser.add_argument(
        "-o",
        type=str,
        required=True,
        help="Output assembly file"
    )

    args = parser.parse_args()

    max_nops = 10

    # Read and parse
    with open(args.i, "r") as fp:
        inp_lines = [AssemblyLine(l) for l in fp.readlines()]

    # Identify a delayed write instruction followed by another one which writes
    # to the same register
    out_lines = []
    for i in range(len(inp_lines)):
        line = inp_lines[i]
        out_lines.append(line)

        # Bypass
        if not line.mnemonic:
            continue

        # Check if it is a delayed write. If not then bypass
        is_delayed = line.mnemonic in ["div", "divu", "rem", "remu", "lw"]
        if not is_delayed:
            continue

        # Get next 2 instructions
        following = []
        for j in range(i+1, len(inp_lines)):
            if inp_lines[j].mnemonic is not None:
                following.append(inp_lines[j])
                if len(following) >= 2:
                    break

        # If any of the instructions targets the same register insert NOPs
        dst = line.operands[0]
        for j, l in enumerate(following):
            if l.operands and l.operands[0] == dst:
                nops = max(0, max_nops - j)
                for _ in range(nops):
                    out_lines.append(" " * 18 + "nop # FIXME: A fixup not to make VeeR cancel a delayed write\n")
                break

    # Write
    with open(args.o, "w") as fp:
        for l in out_lines:
            fp.write(str(l))


if __name__ == "__main__":
    main()
