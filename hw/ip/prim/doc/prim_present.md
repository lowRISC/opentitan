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

Name          | type   | Description
--------------|--------|----------------------------------------------------------
DataWidth     | int    | Block size, can be 32 or 64
KeyWidth      | int    | Key size, can be 64, 80 or 128
NumRounds     | int    | Number of PRESENT rounds, has to be greater than 0
NumPhysRounds | int    | Number of physically instantiated PRESENT rounds (defaults to NumRounds)

Note that by setting `NumRounds = 31` and `NumPhysRounds = 1` we can construct a PRESENT primitive that is suitable for iterative evaluation of a full-round PRESENT pass, where each iteration evaluates one of the 31 rounds.

## Signal Interfaces

Name         | In/Out | Description
-------------|--------|---------------------------------
data_i       | input  | Plaintext input
key_i        | input  | Key input
idx_i        | input  | Round index input
data_o       | output | Output of the ciphertext
key_o        | output | Key output after keyschedule update
idx_o        | output | Round index output after keyschedule update

The `key_o` and `idx_o` are useful for iterative implementations where the state of the scheduled key, as well as the current round index have to be registered in between rounds.
Note that `idx_i` should be initialized to 1 for encryption mode, and to `NumRounds` for decryption mode.

# Theory of Operations

```
             /---------------\
             |               |
idx_i        |               | idx_o
=====/======>|               |=====/======>
 [5]         |               | [5]
             |    PRESENT    |
key_i        |               | key_o
=====/======>|   DataWidth   |=====/======>
 [KeyWidth]  |   KeyWidth    | [KeyWidth]
             |   NumRounds   |
data_i       | NumPhysRounds |  data_o
=====/======>|               |=====/=======>
 [DataWidth] |               |  [DataWidth]
             |               |
             \---------------/
```

The PRESENT module is fully unrolled and combinational, meaning that it does not have any clock, reset or handshaking inputs.
The only inputs are the key and the plaintext, and the only output is the ciphertext.

The internal construction follows the the algorithm described in the original [paper](http://www.lightweightcrypto.org/present/present_ches2007.pdf).
The block size is 64bit and the key size can be either 80bit or 128bit, depending on the security requirements.
In its original formulation, this cipher has 31 rounds comprised of an XOR operation with a round key, followed by the application of an s-box and a permutation layer, as illustrated for the encryption pass below:

```c++
NumRounds = 32;
idx_i = 1;

round_keys = key_derivation(key_i, idx_i);

state = data_i;

for (int i=0; i < NumRounds; i++) {
	state = state ^ round_keys[i];
	state = sbox4_layer(state);
	state = perm_layer(state);
}

data_o = state ^ round_keys[NumRounds-1];
key_o  = round_keys[NumRounds-1];
idx_o  = idx_i + NumRounds;
```

The reduced 32bit block-size variant implemented is non-standard and should only be used for scrambling purposes, since it **is not secure**.
It leverages the same crypto primitives and key derivation functions as the 64bit variant, with the difference that the permutation layer is formulated for 32 instead of 64 elements.
