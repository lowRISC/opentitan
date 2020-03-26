---
title: "Primitive Component: Keccak permutation"
---

# Overview

`prim_keccak` is a single round implementation of the permutation stage in [SHA3 algorithm][fibs-pub-202].
Keccak primitive module assumes the number of rounds is less than or equal to 12 + 2L.
It supports all combinations of the data width described in the [spec][fibs-pub-202].
This implementation is not currently hardened against side-channel or fault injection attacks.
It implements the Keccak_p function.

[fibs-pub-202]: https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.202.pdf

## Parameters

Name  | Type | Description
------|------|----------------------------------------------------------------
Width | int  | state width in bits. can be 25, 50, 100, 200, 400, 800, or 1600

### Derived Parameters

The parameters below are derived parameter from `Width` parameter.

Name     | Type | Description
---------|------|-------------------------------------------------------
W        | int  | number of slices in state. `Width/25`
L        | int  | log2 of `W`
MaxRound | int  | maximum allowed round value. `12 + 2L`
RndW     | int  | bit-width to represent MaxRound. log2 of `MaxRound`

## Signal Interfaces

Signal | Type          | Description
-------|---------------|------------------------------
rnd_i  | input [RndW]  | current round number [0..(MaxRound-1)]
s_i    | input [Width] | state input
s_o    | output[Width] | permutated state output

`s_i` and `s_o` are little-endian bitarrays.
The [SHA3 spec][fibs-pub-202] shows how to convert the bitstream into the 5x5xW state cube.
For instance, bit 0 of the stream maps to `A[0,0,0]`.
The bit 0 in the spec is the first bit of the bitstream.
In `prim_keccak`, `s_i[0]` is the first bit and `s_i[Width-1]` is the last bit.

# Theory of Operations

```
         |                                                          |
rnd_i    |                                                          |
---/---->| -----------------------------------------\               |
 [RndW]  |                                          |               |
         |                                          |               |
s_i      |                                          V               | s_o
===/====>| bit2s() -> chi(pi(rho(theta))) -> iota( ,rnd) -> s2bit() |==/==>
 [Width] |            |-----------keccak_p--------------|           |[Width]
         |                                                          |
```

`prim_keccak` implements "Step Mappings" section in [SHA3 spec][fibs-pub-202].
It is composed of five unique permutation functions, theta, rho, pi, chi, and iota.
Also it has functions that converts bitstream of `Width` into `5x5xW` state and vice versa.

Three constant parameters are defined inside the keccak primitive module.
The rotate position described in phi function is hard-coded as below.
The value is described in the SHA3 specification.

```systemverilog
localparam int PiRotate [5][5] = '{
  //y  0    1    2    3    4     x
  '{   0,   3,   1,   4,   2},// 0
  '{   1,   4,   2,   0,   3},// 1
  '{   2,   0,   3,   1,   4},// 2
  '{   3,   1,   4,   2,   0},// 3
  '{   4,   2,   0,   3,   1} // 4
};
```

The shift amount in rho function is defined as `RhoOffset` parameter.
The value is same as in the specification, but it is used as `RhoOffset % W`.
For instance, `RhoOffset[2][2]` is 171.
If `Width` is 1600, the value used in the design is `171%64`, which is `43`.

The round constant is calculated by the tool `hw/ip/prim/util/keccak_rc.py`.
The recommended default value of 24 rounds is used in this design,
but an argument (changed with the `-r` flag) is provided for reference.
The `keccak_rc.py` script creates 64 bit of constants and the `prim_keccak` module uses only lower bits of the constants if the `Width` is less than 1600.
For instance, if `Width` is 800, lower 32bits of the round constant are used.

