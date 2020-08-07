# OTBN Random Instruction Generator

This directory contains a random instruction generator for OTBN. There
is a wrapper at `../otbn-rig`. Example usage:

```
./hw/ip/otbn/util/otbn-rig -o x.json --asm-output x.asm
```

This generates an assembly file (`x.asm`) containing a random program.
When assembled, loaded into OTBN and executed, the execution trace
should contain roughly 100 instructions. To override this default,
pass the `--size` parameter.

The random program is built from blocks called "snippets". The
simplest possible snippet is a single instruction but more complicated
snippets like short instruction sequences, if/else branches or
function calls are possible. The implementation doesn't currently do
this, but eventually it will generate trees of snippets. For example,
there might be an if/else branch where each arm contains a sequence of
instructions described by a separate snippet.

## The size parameter

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

## JSON output

As well as an assembly file, the example above generates a JSON file
as output. This contains a description of the snippets that form the
generated program. One way to use these snippets is to build a
program: indeed, that's what the instruction generator does
internally.

However, the snippets contain more structured information about the
program and its control flow than just an assembly file. This should
eventually allow "advanced" tricks such as test case shrinking or
maybe test case mutation for fuzzing.

At the moment, we don't do anything with the JSON output, but's it's
quite handy for debugging the generation process.
