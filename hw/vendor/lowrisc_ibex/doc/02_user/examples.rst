.. _examples:

Examples
========

To make use of Ibex it has to be integrated as described in :ref:`core-integration`.

FPGA
----

A minimal example for the `Arty A7 <https://reference.digilentinc.com/reference/programmable-logic/arty-a7/start>`_ FPGA Development board is provided.
In this example Ibex is directly linked to a SRAM memory instance.
Four LEDs from the board are connected to the data bus and are updated each time when a word is written.
The memory is separated into a instruction and data section.
The instructions memory is initialized at synthesis time by reading the output from the software build.
The software writes to the data section the complementary lower for bits of a word every second resulting in blinking LEDs.

Find the description of how to build and program the Arty board in ``examples/fpga/artya7/README.md``.
