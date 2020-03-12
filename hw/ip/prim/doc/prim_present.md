---
title: "Primitive Component: PRESENT Scrambler"
---

# Overview

`prim_present` is an (unhardened) implementation of the encryption pass of the [64bit PRESENT block cipher](https://en.wikipedia.org/wiki/PRESENT).
It is a fully unrolled combinational implementation that supports both key lengths specified in the paper (80bit and 128bit).
Further, the number of rounds is fully configurable, and the primitive supports a 32bit block cipher flavor which is not specified in the original paper.

It should be noted, however, that reduced-round and/or 32bit versions **are not secure** and must not be used in a setting where cryptographic cipher strength is required.
I.e., this primitive is only intended to be used as a lightweight data scrambling device.

## Parameters

Name         | type   | Description
-------------|--------|----------------------------------------------------------
DataWidth    | int    | Block size, can be 32 or 64
KeyWidth     | int    | Key size, can be 64, 80 or 128
NumRounds    | int    | Number of PRESENT rounds, has to be greater than 0

## Signal Interfaces

Name         | In/Out | Description
-------------|--------|---------------------------------
data_i       | input  | Plaintext input
key_i        | input  | Key input
data_o       | output | Output of the ciphertext

# Theory of Operations

```
             /---------------\
             |               |
             |    PRESENT    |
key_i        |               |
=====/======>|   DataWidth   |
 [KeyWidth]  |   KeyWidth    |
             |   NumRounds   |
data_i       |               |  data_o
=====/======>|               |=====/=======>
 [DataWidth] |               |  [DataWidth]
             |               |
             \---------------/
```

The PRESENT module is fully unrolled and combinational, meaning that it does not have any clock, reset or handshaking inputs.
The only inputs are the key and the plaintext, and the only output is the ciphertext.

The internal construction follows the the algorithm described in the original [paper](http://www.lightweightcrypto.org/present/present_ches2007.pdf).
The block size is 64bit and the key size can be either 80bit or 128bit, depending on the security requirements.
In its original formulation, this cipher has 31 rounds comprised of an XOR operation with a round key, followed by the application of an s-box and a permutation layer:

```c++

round_keys = key_derivation(key_i);

state = data_i;

for (int i=1; i < 32; i++) {
	state = state ^ round_keys[i];
	state = sbox4_layer(state);
	state = perm_layer(state);
}

data_o = state ^ round_keys[32];
```

The reduced 32bit block-size variant implemented is non-standard and should only be used for scrambling purposes, since it **is not secure**.
It leverages the same crypto primitives and key derivation functions as the 64bit variant, with the difference that the permutation layer is formulated for 32 instead of 64 elements.
