# AES HWIP Technical Specification

{{#block-dashboard aes}}

# Overview

This document specifies the AES hardware IP functionality.
[Advanced Encryption Standard (AES)](https://www.nist.gov/publications/advanced-encryption-standard-aes) is the primary symmetric encryption and decryption mechanism used in OpenTitan protocols.
The AES unit is a cryptographic accelerator that accepts requests from the processor to encrypt or decrypt 16 byte blocks of data.
It is attached to the chip interconnect bus as a peripheral module and conforms to the [Comportable guideline for peripheral functionality.](../../../doc/contributing/hw/comportability/README.md)


## Features

The AES unit supports the following features:

- Encryption/Decryption using AES-128/192/256 in the following cipher block modes:
  - Electronic Codebook (ECB) mode,
  - Cipher Block Chaining (CBC) mode,
  - Cipher Feedback (CFB) mode (fixed data segment size of 128 bits, i.e., CFB-128),
  - Output Feedback (OFB) mode, and
  - Counter (CTR) mode.
- Support for AES-192 can be removed to save area, and is enabled/disabled using a compile-time Verilog parameter
- First-order masking of the cipher core using domain-oriented masking (DOM) to deter side-channel analysis (SCA), can optionally be disabled using compile-time Verilog parameters (for more details see [Security Hardening below](#side-channel-analysis))
- Latency per 16 byte data block of 12/14/16 clock cycles (unmasked implementation) and 56/66/72 clock cycles (DOM) in AES-128/192/256 mode
- Automatic as well as software-initiated reseeding of internal pseudo-random number generators (PRNGs) with configurable reseeding rate resulting in max entropy consumption rates ranging from 286 Mbit/s to 0.035 Mbit/s (at 100 MHz).
- Countermeasures for deterring fault injection (FI) on the control path (for more details see [Security Hardening below](#fault-injection))
- Register-based data and control interface
- System key-manager interface for optional key sideload to not expose key material to the processor and other hosts attached to the system bus interconnect.
- On-the-fly round-key generation in parallel to the actual encryption/decryption from a single initial 128/192/256-bit key provided through the register interface (for more details see [Theory of Operations below](#theory-of-operations))

This AES unit targets medium performance (16 parallel S-Boxes, \~1 cycle per round for the unmasked implementation, \~5 cycles per round for the DOM implementation).
High-speed, single-cycle operation for high-bandwidth data streaming is not required.

Cipher modes other than ECB, CBC, CFB, OFB and CTR are beyond this version of the AES unit but might be supported in future versions.
Galois/Counter Mode (GCM) can be implemented by leveraging [Ibex](../rv_core_ibex/README.md) for the GHASH operation as demonstrated in [OpenTitan's library of cryptographic implementations](https://github.com/lowRISC/opentitan/tree/master/sw/device/lib/crypto).


## Description

The AES unit is a cryptographic accelerator that accepts requests from the processor to encrypt or decrypt 16B blocks of data.
It supports AES-128/192/256 in Electronic Codebook (ECB) mode, Cipher Block Chaining (CBC) mode, Cipher Feedback (CFB) mode (fixed data segment size of 128 bits, i.e., CFB-128), Output Feedback (OFB) mode and Counter (CTR) mode.
For more information on these cipher modes, refer to [Recommendation for Block Cipher Modes of Operation](https://nvlpubs.nist.gov/nistpubs/Legacy/SP/nistspecialpublication800-38a.pdf).
Galois/Counter Mode (GCM) can be implemented using [Ibex](../rv_core_ibex/README.md) for the GHASH operation as demonstrated in [OpenTitan's library of cryptographic implementations](https://github.com/lowRISC/opentitan/tree/master/sw/device/lib/crypto).
To improve the performance of GCM, instructions of the [RISC-V Bit-Manipulation Extension of Ibex](https://ibex-core.readthedocs.io/en/latest/03_reference/instruction_decode_execute.html#arithmetic-logic-unit-alu) can be leveraged.
In particular, carry-less multiply instructions can help to speed up the GHASH operation.
For details on GCM, refer to [Recommendation for Block Cipher Modes of Operation: Galois/Counter Mode (GCM) and GMAC](https://nvlpubs.nist.gov/nistpubs/Legacy/SP/nistspecialpublication800-38d.pdf).
Other cipher modes might be added in future versions.

The AES unit is attached to the chip interconnect bus as a peripheral module.
Communication with the processor happens through a set of control and status registers (CSRs).
This includes input/output data and key, as well as status and control information.
Future versions of the AES unit might include a separate interface through which a possible system key manager can provide the key without exposing it to the processor or other hosts attached to the system bus interconnect.
