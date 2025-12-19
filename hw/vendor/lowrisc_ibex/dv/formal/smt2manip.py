# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# Original author: Louis-Emile Ploix
# SPDX-License-Identifier: Apache-2.0

from pathlib import Path
import re
import argparse

# Yosys smt2 files encode assertions and assumptions fairly clearly,
# so it's not too difficult to move them around just by regexp.

parser = argparse.ArgumentParser(prog="smt2manip", description="Does aig-manip select for smt2 files.")
parser.add_argument("yosys_smt2", help="Input smt2 file")
parser.add_argument("smt2out", help="Output smt2 file")
parser.add_argument("step", type=int, help="Step number")
parser.add_argument("props", nargs="*", help="Property list, or if empty all of them for the given step.")
args = parser.parse_args()

smt2 = Path(args.yosys_smt2).read_text()

lines = smt2.split("\n")
mapped = []

to_assume = []
delete = []

for line in lines:
    m = re.match(r"; yosys-smt2-assert ([0-9]+) ([^ ]+)", line)
    if m is not None:
        id = m[1]
        name = m[2][6:].split("$")[0]
        assert name.startswith("Step")
        [step, name] = name.split("_", maxsplit=1)
        step = int(step[4:])

        if name.endswith("_Cover") or step > args.step or (step == args.step and len(args.props) > 0 and name not in args.props):
            print(f"Delete {name} ({id})")
            delete.append(id)
        elif step < args.step:
            print(f"Assert2Assume {name} ({id})")
            to_assume.append(id)
        else:
            print(f"Keep {name} ({id})")
        mapped.append(line)
        continue

    m = re.match(r"  \(\|top_a ([0-9]+)\| state\)", line)
    if m is not None:
        if m[1] in to_assume or m[1] in delete:
            continue
        mapped.append(line)
        continue

    if line == "(define-fun |top_u| ((state |top_s|)) Bool (and":
        mapped.append(line)
        for id in to_assume:
            mapped.append(f"  (|top_a {id}| state)")
        continue

    mapped.append(line)

Path(args.smt2out).write_text("\n".join(mapped))
