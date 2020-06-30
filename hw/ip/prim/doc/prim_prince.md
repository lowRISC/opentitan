---
title: "Primitive Component: PRINCE Scrambler"
---

# Overview

`prim_prince` is an (unhardened) implementation of the [64bit PRINCE block cipher](https://en.wikipedia.org/wiki/Prince_(cipher)).
It is a fully unrolled combinational implementation with a configurable number of rounds (data and key state registers placed half-way in the design can optionally be enabled).
Due to the mirrored construction of this cipher, the same circuit can be used for encryption and decryption, as described below.
Further, the primitive supports a 32bit block cipher flavor which is not specified in the original paper.

It should be noted, however, that reduced-round and/or 32bit versions **are not secure** and must not be used in a setting where cryptographic cipher strength is required.
I.e., this primitive is only intended to be used as a lightweight data scrambling device.

This [paper](https://csrc.nist.gov/csrc/media/events/lightweight-cryptography-workshop-2015/documents/papers/session7-maene-paper.pdf) compares several lightweight ciphers, where PRINCE has been found to be the fastest candidate with the lowest circuit complexity among the algorithms compared.

## Parameters

Name           | type   | Description
---------------|--------|----------------------------------------------------------
DataWidth      | int    | Block size, can be 32 or 64.
KeyWidth       | int    | Key size, can be 64 for block size 32, or 128 for block size 64
NumRounds      | int    | Half the number of the reflected PRINCE rounds. Can range from 1 to 5. The effective number of non-linear layers is 2 + 2 * NumRounds.
UseOldKeySched | bit    | If set to 1, fall back to the original keyschedule (not recommended). Defaults to 0.
HalfwayDataReg | bit    | If set to 1, instantiates a data register half-way in the data path
HalfwayKeyReg  | bit    | If set to 1, instantiates a key register half-way in the data path. This is only required if the key is not static and changes with every new data input.

## Signal Interfaces

Name         | In/Out | Description
-------------|--------|---------------------------------
clk_i        | input  | Clock input
rst_ni       | input  | Reset input
valid_i      | input  | Data valid input
data_i       | input  | Plaintext input
data_i       | input  | Plaintext input
key_i        | input  | Key input
dec_i        | input  | Assert for decryption
valid_o      | output | Data valid output
data_o       | output | Output of the ciphertext

# Theory of Operations

```
               /-----------------\
clk_i / rst_ni |                 |
-------------->|                 |
dec_i          |                 |
-------------->|     PRINCE      |
valid_i        |                 | valid_o
-------------->|    DataWidth    |--------------->
key_i          |    KeyWidth     |
=====/========>|    NumRounds    |
 [KeyWidth]    |  UseOldKeySched | data_o
               |  HalfwayDataReg |=======/=======>
data_i         |  HalfwayKeyReg  | [DataWidth]
=====/========>|                 |
 [DataWidth]   |                 |
               |                 |
               \-----------------/
```

The PRINCE module is fully unrolled and combinational by default.
But since data and key state registers can optionally be enabled, the primitive also has a clock, reset and valid input besides the key and plaintext inputs.
On the output side it exposes the ciphertext with its corresponding valid signal.

The internal construction follows the the algorithm described in the original [paper](https://eprint.iacr.org/2012/529.pdf).
The block size is 64bit and the key size is 128bit.
In its original formulation, this cipher has 11 rounds (but 12 non-linear layers), which are arranged in a mirrored structure, which allows the same circuit to be used for encryption and decryption with a lightweight tweak applied to the key:

```c++
k0, k0_prime, k1 = key_derivation(key_i, dec_i);

// decryption mode
if (dec_i) {
      swap(k0, k0_prime);
      k1 ^= ALPHA_CONSTANT;
}

state = data_i ^ k0;

state ^= k1;
state ^= ROUND_CONSTANT[0];

// forward pass
for (int i=1; i < 6; i++) {
      state = sbox4_layer(state);
      state = mult_layer(state);
      state = shiftrows_layer(state);
      state ^= ROUND_CONSTANT[i]
      data_state ^= (k & 0x1) ? k0 : k1;
}

// middle part
state = sbox4_layer(state);
state = mult_layer(state);
state = sbox4_inverse_layer(state);

// reverse pass
for (int i=6; i < 11; i++) {
      data_state ^= (k & 0x1) ? k1 : k0;
      state ^= ROUND_CONSTANT[i]
      state = shiftrows_inverse_layer(state);
      state = mult_layer(state);
      state = sbox4_inverse_layer(state);
}

state ^= ROUND_CONSTANT[11];
state ^= k1;

data_o = state ^ k0_prime;
```
The multiplicative layer is an involution, meaning that it is its own inverse and it can hence be used in the reverse pass without inversion.

It should be noted that the actual choice of the `ALPHA_CONSTANT` used in the key tweak can have security impacts as detailed in [this paper](https://eprint.iacr.org/2015/372.pdf).
The constant chosen by the designers of PRINCE does not have these issues - but proper care should be taken if it is decided to modify this constant.
Also, [this paper](https://eprint.iacr.org/2014/656.pdf) proposes an improved key schedule to fend against attacks on the FX structure of PRINCE (see Appendix C), and this improvement has been incorporated in this design.
The improvement involves alternating the keys `k0` and `k1` between rounds, as opposed to always using the same key `k1`.


The reduced 32bit variant mentioned above and all reduced round variants are non-standard and must only be used for scrambling purposes, since they **are not secure**.
The 32bit variant leverages the same crypto primitives and key derivation functions as the 64bit variant, with the difference that the multiplication matrix is only comprised of the first two block diagonal submatrices (^M0 and ^M1 in the paper), and the shiftrows operation does not operate on nibbles but pairs of 2 bits instead.


