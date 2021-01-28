# OTBN Random Instruction Generator

This directory contains a random instruction generator for OTBN called
`otbn-rig`. This is intended to be run in multiple phases. If you just
want to generate some random binaries, it might be easier to call the
wrapper at `../uvm/gen-binaries.py`.

At the moment, there are two sub-commands: `gen` and `asm`. In future,
we might add more (to do things like test case mutation or shrinking).

## The gen command

The `gen` command is in charge of actually generating a random
program. This program is written to stdout in an JSON format. This
format may change over time, but it is understood by the `asm`
command.

Example usage:
```
hw/ip/otbn/dv/rig/otbn-rig gen --seed 123 --size 1000 >foo.json
```

To control random generation, there is a `--seed` parameter. The
output should be stable for a fixed seed. If not specified, the seed
is zero.

To support testing with the `START_ADDR` register, which allows the
host processor to control OTBN's reset address, there is a
`--start-addr` parameter. By default this is zero.

### The size parameter

The `--size` parameter is used to control how big the program grows. A
snippet with a single unconditionally executed instruction has a size
of one. A snippet containing a sequence of `N` instructions has a size
of `N`. For a more interesting example, consider an if/else branch
that would look something like this in C:

```C
    if (A) {
        B;
    } else {
        C;
    }
```

If calculating `A` takes `a` cycles and `B` and `C` have a size of `b`
and `c` respectively, then the entire snippet has size `a + max(b,
c)`. The general idea is that the size taken by a snippet is an upper
bound on the number of instructions that it causes the processor to
execute. This might not be a strict upper bound: for example, it won't
be strict if `a != b` in the if/else snippet above.

### Snippets

The random program is built from blocks called "snippets". The
simplest possible snippet is a sequence of straight-line instructions.
There are also more complicated snippets like conditional branches and
loops. The JSON output format represents this tree of snippets.

### Initialised data

The generated program is designed never to trigger architecturally
unspecified behaviour. It might trigger errors, but its execution will
never depend on things like the initial contents of the register file
or uninitialised memories.

To provide some data so that RIG can generate load instructions even
near the start of the run, the generated program also includes a few
words of (randomly) initialised data, scattered around dmem.

## The asm command

Once a random program has been generated, the `asm` command can be
used to convert it to an assembly listing. This, in turn, can be
assembled and linked using the toolchain in `hw/ip/otbn/util`.

Unlike the `gen` command, this step does no random generation: it's a
deterministic translation from the JSON input to assembly and linker
script output.

Example usage:
```
hw/ip/otbn/dv/rig/otbn-rig asm --output foo foo.json
```

When given the `--output` parameter, this command generates two output
files. With `--output foo`, it generates `foo.s` and `foo.ld`. These
are an assembly listing and a linker script, respectively.

To assemble and link, use commands like:
```
hw/ip/otbn/util/otbn-as -o foo.o foo.s
hw/ip/otbn/util/otbn-ld -o foo.elf -T foo.ld foo.o
```
This is automated in the `gen-binaries.py` wrapper described above.

Occasionally, it's helpful to just read the assembly listing for a
JSON file. To do this, run the command with no `--output` parameter to
see the assembly listing on stdout. The linker script will not be
generated.
