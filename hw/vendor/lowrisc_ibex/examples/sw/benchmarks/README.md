# Benchmarks

This directory contains benchmarks that can be run on ibex simple system.
Benchmarks may rely on code external to this directory (e.g. it may be found in
`vendor/`) see the specific benchmark information below for details on how to
build and run each benchmark and where benchmark code is located.

## Building Simulation

All of these benchmarks run on Simple System. A verilator simulation suitable
for running them can be built with:

```
fusesoc --cores-root=. run --target=sim --setup --build lowrisc:ibex:ibex_simple_system --RV32M=1 --RV32E=0
```

See examples/simple_system/README.md for full details.

## Coremark

Coremark (https://www.eembc.org/coremark/ https://github.com/eembc/coremark) is
an industry standard benchmark with results available for a wide variety of
systems.

The Coremark source is vendored into the Ibex repository at
`vendor/eembc_coremark`. Support structure and a makefile to build Coremark for
running on simple system is found in `examples/sw/benchmarks/coremark`.

To build Coremark:

```
make -C ./examples/sw/benchmarks/coremark/
```

To run Coremark (after building a suitable simulator binary, see above):

```
build/lowrisc_ibex_ibex_simple_system_0/sim-verilator/Vibex_simple_system --meminit=ram,examples/sw/benchmarks/coremark/coremark.elf
```

The simulator outputs the performance counter values observed for the benchmark
(the counts do not include anything from pre or post benchmark loops).

Coremark should output (to `ibex_simple_system.log`) something like the
following:

```
2K performance run parameters for coremark.
CoreMark Size    : 666
Total ticks      : 4244465
Total time (secs): 8
Iterations/Sec   : 1
Iterations       : 10
Compiler version : GCC
Compiler flags   :
Memory location  :
seedcrc          : 0xe9f5
[0]crclist       : 0xe714
[0]crcmatrix     : 0x1fd7
[0]crcstate      : 0x8e3a
[0]crcfinal      : 0xfcaf
Correct operation validated. See README.md for run and reporting rules.
```

A Coremark score is given as the number of iterations executed per second. The
Coremark binary is hard-coded to execute 10 iterations (see
`examples/sw/benchmarks/coremark/Makefile` if you wish to alter this).  To obtain
a useful Coremark score from the simulation you need to choose a clock speed the
Ibex implementation you are interested in would run at, e.g. 100 MHz, taking
the above example:

* 10 iterations take 4244465 clock cycles
* So at 100 MHz Ibex would execute (100 * 10^6) / (4244465 / 10) = 235.6
  Iterations in 1 second.
* Coremark (at 100 MHz) is 235.6

Coremark/MHz is often used instead of a raw Coremark score. The example above
gives a Coremark/MHz of 2.36 (235.6 / 100 rounded to 2 decimal places).

To directly produce Coremark/MHz from the number of iterations (I) and total
ticks (T) use the follow formula:

```
Coremark/MHz = (10 ^ 6) * I / T
```

Note that `core_main.c` from Coremark has had a minor modification to prevent it
from reporting an error if it executes for less than 10 seconds. This violates
the run reporting rules (though does not effect benchmark execution). It is
trivial to restore `core_main.c` to the version supplied by EEMBC in the
Coremark repository if an official result is desired.
