{{% lowrisc-doc-hdr Primitive Component: LFSR }}

{{% section1 Overview }}

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


{{% section2 Parameters }}

Name      | type   | Description
----------|--------|----------------------------------------------------------
LfsrType  | string | LFSR form, can be `"GAL_XOR"` or `"FIB_XNOR"`
LfsrDw    | int    | Width of the LFSR
InDw      | int    | Width of the entropy input
OutDw     | int    | Width of the LFSR state to be output (`lfsr_q[OutDw-1:0]`)
Seed      | logic  | Initial state of the LFSR, must be nonzero for XOR and non-all-ones for XNOR forms.
Custom    | logic  | Custom polynomial coefficients of length LfsrDw.
MaxLenSVA | bit    | Enables maximum length assertions, use only in sim and FPV.

{{% section2 Signal Interfaces }}

Name          | In/Out | Description
--------------|--------|---------------------------------
en_i          | input  | Lfsr enable
data_i[InDw]  | input  | Entropy input
data_o[OutDw] | output | LFSR state output.

{{% section1 Theory of Opeations }}

```
           /-----------\
en_i       |           |
---------->|   lfsr    |
           |           |
data_i     |  LfsrDw   |       data_o
=====/====>| LfsrType  |=======/=======>
 [InDw]    |   InDw    |    [OutDw]
           |   OutDw   |
           |   Seed    |
           |  Custom   |
           | MaxLenSVA |
           |           |
           \-----------/
```

The LFSR module has an enable input and an additional entropy input that is
XOR'ed into the LFSR state (connect to zero if this feature is unused). The data
output contains the lower bits of the LFSR state from `OutDw-1` downto `0`. As
the entropy input may cause the LFSR to jump into its parasitic state
(all-zero for XOR, all-ones for XNOR), the LFSR state transition function
contains a lockup protection which re-seeds the state once this condition is
detected.

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
