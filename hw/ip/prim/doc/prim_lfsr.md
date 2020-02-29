---
title: "Primitive Component: LFSR"
---

# Overview

`prim_lfsr` is a parameterized linear feedback shift register (LFSR)
implementation that supports Galois (XOR form) and Fibonacci (XNOR form)
polynomials. The main difference between Galois and Fibonacci is that the
former has a shorter critical timing path since the XOR Gates are interleaved
with the shift register, whereas the latter combines several shift register taps
and reduces them with an XNOR tree. For more information, refer to
[this page](https://en.wikipedia.org/wiki/Linear-feedback_shift_register). Both
LFSR flavors have maximal period (`2^LfsrDw - 1`). The recommendation is to use
the Galois type and fall back to the Fibonacci type depending on the polynomial
width availability in the lookup table (see below).


## Parameters

Name         | type   | Description
-------------|--------|----------------------------------------------------------
LfsrType     | string | LFSR form, can be `"GAL_XOR"` or `"FIB_XNOR"`
LfsrDw       | int    | Width of the LFSR
EntropyDw    | int    | Width of the entropy input
StateOutDw   | int    | Width of the LFSR state to be output (`lfsr_q[StateOutDw-1:0]`)
DefaultSeed  | logic  | Initial state of the LFSR, must be nonzero for XOR and non-all-ones for XNOR forms.
CustomCoeffs | logic  | Custom polynomial coefficients of length LfsrDw.
MaxLenSVA    | bit    | Enables maximum length assertions, use only in sim and FPV.

## Signal Interfaces

Name                 | In/Out | Description
---------------------|--------|---------------------------------
seed_en_i            | input  | External seed input enable
seed_i[LfsrDw]       | input  | External seed input
lfsr_en_i            | input  | Lfsr enable
entropy_i[EntropyDw] | input  | Entropy input
state_o[StateOutDw]  | output | LFSR state output.

# Theory of Operations

```
             /----------------\
seed_en_i    |                |
------------>|      lfsr      |
seed_i       |                |
=====/======>|     LfsrDw     |
 [LfsrDw]    |    LfsrType    |
lfsr_en_i    |   EntropyDw    |
------------>|   StateOutDw   |
entropy_i    |   DefaultSeed  |  state_o
=====/======>|  CustomCoeffs  |=====/=======>
 [EntropyDw] |   MaxLenSVA    |  [StateOutDw]
             |                |
             \----------------/
```

The LFSR module has an enable input and an additional entropy input that is
XOR'ed into the LFSR state (connect to zero if this feature is unused). The
state output contains the lower bits of the LFSR state from `StateOutDw-1`
downto `0`. As the entropy input may cause the LFSR to jump into its parasitic
state (all-zero for XOR, all-ones for XNOR), the LFSR state transition function
contains a lockup protection which re-seeds the state with `DefaultSeed` once
this condition is detected.

The LFSR contains an external seed input `seed_i` which can be used to load a
custom seed into the LFSR by asserting `seed_en_i`. This operation takes
precedence over internal state updates. If the external seed happens to be a
parasitic state, the lockup protection feature explained above will reseed the
LFSR with the `DefaultSeed` in the next cycle.

The LFSR coefficients are taken from an internal set of lookup tables with
precomputed coefficients. Alternatively, a custom polynomial can be provided
using the `Custom` parameter. The lookup tables contain polynomials for both
LFSR forms and range from 4bit to 64bit for the Galois form and 3bit to 168bit
for the Fibonacci form. The polynomial coefficients have been obtained from
[this page](https://users.ece.cmu.edu/~koopman/lfsr/) and
[Xilinx application note 52](https://www.xilinx.com/support/documentation/application_notes/xapp052.pdf).
The script `./script/get-lfsr-coeffs.py` can be used to download, parse and dump
these coefficients in SV format as follows:
```
$ script/get-lfsr-coeffs.py -o <output_file>
```
The default is to get the Galois coefficients. If the Fibonacci coefficients
are needed, add the `--fib` switch to the above command.

The implementation of the state transition function of both polynomials have
been formally verified. Further, all polynomials up to 34bit in length have been
swept through in simulation in order to ensure that they are of
maximal-length.
