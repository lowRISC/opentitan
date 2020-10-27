# OTBN code snippet collection

This directory contains some code snippets that give examples of how
to do various tasks in OTBN code.

  - `modexp.s`: An example of how to do modular exponentiation.
  - `pseudo-ops.s`: An example of the pseudo-operations supported by the OTBN ISA.
  - `mul256.s`: An example of a 256x256 bit multiply using the MULQACC
    instruction.
  - `mul384.s`: An example of a 384x384 bit multiply using the MULQACC
    instruction.
  - `barrett384.s`: An example of a modular multiplication kernel based on
    Barrett reduction.

Also included in this directory is a Makefile fragment that can be
used to assemble and link the snippets. This can be used standalone or
included in another Makefile.
