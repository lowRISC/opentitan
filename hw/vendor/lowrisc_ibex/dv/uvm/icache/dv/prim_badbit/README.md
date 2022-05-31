Badbit RAM
==========

This is an SRAM wrapper that allows a testbench to force bit errors onthe read interface.

This works as a dummy technology library.
Instantiate it by adding setting `PRIM_DEFAULT_IMPL` to prim_pkg::ImplBadbit (see the README.md in the prim directory for details).
To use it, bind a module or interface into an instance of `prim_badbit_ram_1p` and force the value of `bad_bit_mask`, which is XOR'd with rdata.

To make this easier to use, we don't vary the width of `bad_bit_mask` with the `Width` parameter: it's a constant 128.
This means that the bound interface doesn't need to be parameterised.
