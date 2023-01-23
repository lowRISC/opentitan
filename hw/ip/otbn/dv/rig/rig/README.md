# OTBN Random Instruction Generator - Internals

This directory contains the internal part of the random instruction generator (RIG).
This document aims to help with the general understanding of the inner workings of RIG.

## Overall Structure
`rig.py` calls `snippet_gens.py` to generate a configured list of smaller snippet generators.
The main constraint while generating these snippets is called `fuel` and it's an upper bound for the number of instructions to execute.
The `SnippetGens` class involves a list of these smaller snippet generators defined in `_CLASSES`.

This main script also constructs a `Program` and a `Model`.
`Program` reflects both data memory that gets initialised and also the instruction memory that gets set with the generated snippets.

The generated program then gets used in `otbn-rig` (which lives in the parent directory) to create proper output files to simulate the generated instructions.

## Snippet Generators
These generators are split up into two lists.
The list called `_cont_generators` is the list of snippet generators that will not produce snippets that end the program.
The other list `_end_generators` consists of generators that produces either an `ECALL` or a fault to finish the program.
The type of fault that the snippet generator creates is in its name (e.g. `BadInsn` snippet generator will generate snippets that end with an illegal instruction).

### Configuring a Snippet Generator
Each snippet generator has its own weight specified in the `configs` folder.
In its `README`, there is a detailed explanation about how to configure specific `.yaml` files for wanted behavior.
For a brief summary for the currently existing `.yaml` files:

- `default.yaml`: This is the default configuration when configuring snippet generators.
Picks a configuration file at random from below with specified weights.
- `base.yaml` : Consists of all possible snippet generators with their default weights relative to each other.
- `loopy.yaml`: A custom configuration that generates hundred times as many loop instructions compared to the `base` configuration.
- `straigh-line.yaml`: A custom configuration that does not generate any branches, hence the name.

## Abstract Models in RIG
In order to generate concise programs that don't run into architectural problems RIG needs to have an idea about how OTBN works, what's a memory, a register etc.
This is all handled in `model.py` in which different classes for different models exists.
A list of them includes:
- `CallStack`: Abstract model of the `x1` call stack
- `LoopStack`: An abstract model of the loop stack.
It has a `stuck` counter for keeping track of pop addresses that doesn't match - related with "Loop Warping".
- `Model`: Abstract model of the processor and the memories.
Holds tracks of registers and memory locations that have defined values at a current instruction stream.
Note that while in operation there can be more than two models instantiated to enable RIG to make decisions based on the current state of the program, and to maintain the consistency of the program state.
For more details see `loop.py`.
