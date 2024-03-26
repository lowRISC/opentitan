# Overview

This document specifies the [Ascon](https://ascon.iaik.tugraz.at/) hardware IP functionality.
Ascon is a sponge-based, single pass, online Authenticated Encryption Scheme (that can also be used for hashing).
It was selected by [NIST as the winner](https://www.nist.gov/news-events/news/2023/02/nist-selects-lightweight-cryptography-algorithms-protect-small-devices) of the NIST lightweight cryptography competition and is soon to be standardized.


## Features

The Ascon units supports the following features:

* Authenticated encryption/decryption using either Ascon-128 (64 bit block size, 6 rounds per block update) or Ascon-128a (128 bit block size, 8 rounds per block update), whichever variant is standardized by NIST[^1], with a key and tag size of 128 bit, which leads to 128 bit security, and a state size of 320 bits.
* Support for Hashing might be implemented at a later time.
* First-order masking of the cipher core using domain-oriented masking (DOM) to deter side-channel analysis (SCA) is planned for the final version.
* The latency of the Ascon permutation per 64/128 bit block is 6/8 clock cycles (unmasked) and presumably 12/16 clock cycles (DOM) for Ascon-128/Ascon-128a.
Overall, 1 cycle is needed to absorb the data, 6/8 cycles are needed for the permutation and again 1 cycle to extract the output.
However, the extraction and absorption are done simultaneously.
Thus, in total, for long messages, the latency between a corresponding plaintext-ciphertext block is 1 cycle,
and the latency between two consecutive ciphertext/plaintext blocks is 7/9 cycles; assuming large input sizes such that initialization and tag computation are negligible.
* Automatic as well as software-initiated reseeding of internal pseudo-random number generators (PRNGs).
This will be implemented in the final version.
* Countermeasures for deterring fault injection (FI) on the control path (for more details see [Security Hardening](#security-hardening-13)).
* Register-based data and control interface.
* System key manager interface for optional key sideload to not expose key material to the processor and other hosts attached to the system bus interconnect.

This Ascon unit targets medium performance (~1 clock cycle per round for the unmasked implementation).
High-speed, multiple rounds per clock cycles for high-bandwidth data streaming is not required.


## Description

The Ascon unit is a cryptographic accelerator that accepts requests from the processor to encrypt or decrypt pairs of associated data A and messages M. A and M are divided into blocks, where each block is 64/128 bits, except the last block that can be potentially smaller.
Empty strings are allowed, where either A, M or both are empty.
The unit also takes a unique nonce N per each pair (A,M).
The encryption request outputs a ciphertext C of the same size as M, and a 128-bit tag T.
The decryption request checks the validity of the ciphertext with respect to the key, N and A, and returns a failure code if the ciphertext is invalid.
The algorithm requires that the implementation outputs a decrypted message M of the same size as M only if M is valid.
Implementing this fully in hardware is infeasible, however, as the plaintext size is variable and would require large dedicated buffer memory.
Our Ascon unit thus outputs the decrypted plaintext before it is verified and SW interfacing the Ascon unit must make sure not to use such plaintext if it is invalid.

The Ascon unit consists of 5 main components:
encrypt/decrypt FSM, Ascon permutation round, the functionality of initializing or updating the internal state and extracting ciphertext (dubbed as duplex switch), the tag extractor (for releasing the tag), and tag comparator (for checking the tag validity).

The Ascon unit is attached to the chip interconnect bus as a peripheral module.
Communication with the processor happens through a set of control and status registers (CSRs).
This includes the input/output data, key, nonce, as well as status and control information.

[^1]: There are two main variants: Ascon128 and Ascon 128a. Both variants use 12 rounds for initialization and finalization. They differ in the input block size and the rounds per update.
    "Ascon v1.2. Submission to NIST." [https://csrc.nist.gov/CSRC/media/Projects/lightweight-cryptography/documents/round-2/spec-doc-rnd2/ascon-spec-round2.pdf](https://csrc.nist.gov/CSRC/media/Projects/lightweight-cryptography/documents/round-2/spec-doc-rnd2/ascon-spec-round2.pdf). Accessed 21 Aug. 2023.
    According to [https://csrc.nist.gov/csrc/media/Presentations/2023/update-on-standardization-of-ascon-family/images-media/sess-6-turan-bcm-workshop-2023.pdf](https://csrc.nist.gov/csrc/media/Presentations/2023/update-on-standardization-of-ascon-family/images-media/sess-6-turan-bcm-workshop-2023.pdf) either both or only Ascon-128 will be standardized. Further, there might be no dedicated Hash function but only a standardized XOF form.
    Non standardized extensions like a PRF could be implemented with a marginal overhead in a future version.
