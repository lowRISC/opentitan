---
title: "AES HWIP Technical Specification"
---


# Overview

This document specifies the AES hardware IP functionality.
[Advanced Encryption Standard (AES)](https://www.nist.gov/publications/advanced-encryption-standard-aes) is the primary symmetric encryption and decryption mechanism used in OpenTitan protocols.
The AES unit is a cryptographic accelerator that accepts requests from the processor to encrypt or decrypt 16 byte blocks of data.
It is attached to the chip interconnect bus as a peripheral module and conforms to the [Comportable guideline for peripheral functionality.]({{< relref "doc/rm/comportability_specification" >}})


## Features

The AES unit supports the following features:

- Encryption/Decryption using AES-128/192/256 in the following cipher block modes:
  - Electronic Codebook (ECB) mode,
  - Cipher Block Chaining (CBC) mode,
  - Cipher Feedback (CFB) mode (fixed data segment size of 128 bits, i.e., CFB-128),
  - Output Feedback (OFB) mode, and
  - Counter (CTR) mode.
- Support for AES-192 can be removed to save area, and is enabled/disabled using a compile-time Verilog parameter
- First-order masking of the cipher core using domain-oriented masking (DOM) to aggravate side-channel analysis (SCA), can optionally be disabled using compile-time Verilog parameters (for more details see [Security Hardening below]({{< relref "#side-channel-analysis" >}}))
- Latency per 16 byte data block of 12/14/16 clock cycles (unmasked implementation) and 56/66/72 clock cycles (DOM) in AES-128/192/256 mode
- Automatic as well as software-initiated reseeding of internal pseudo-random number generators (PRNGs) with configurable reseeding rate resulting in max entropy consumption rates ranging from 286 Mbit/s to 0.035 Mbit/s (at 100 MHz).
- Countermeasures for aggravating fault injection (FI) on the control path (for more details see [Security Hardening below]({{< relref "#fault-injection" >}}))
- Register-based data and control interface
- System key-manager interface for optional key sideload to not expose key material to the processor and other hosts attached to the system bus interconnect.
- On-the-fly round-key generation in parallel to the actual encryption/decryption from a single initial 128/192/256-bit key provided through the register interface (for more details see [Theory of Operations below]({{< relref "#theory-of-operations" >}}))

This AES unit targets medium performance (16 parallel S-Boxes, \~1 cycle per round for the unmasked implementation, \~5 cycles per round for the DOM implementation).
High-speed, single-cycle operation for high-bandwidth data streaming is not required.

Cipher modes other than ECB, CBC, CFB, OFB and CTR are beyond this version of the AES unit but might be supported in future versions.


## Description

The AES unit is a cryptographic accelerator that accepts requests from the processor to encrypt or decrypt 16B blocks of data.
It supports AES-128/192/256 in Electronic Codebook (ECB) mode, Cipher Block Chaining (CBC) mode, Cipher Feedback (CFB) mode (fixed data segment size of 128 bits, i.e., CFB-128), Output Feedback (OFB) mode and Counter (CTR) mode.
For more information on these cipher modes, refer to [Recommendation for Block Cipher Modes of Operation](https://nvlpubs.nist.gov/nistpubs/Legacy/SP/nistspecialpublication800-38a.pdf).
Other cipher modes might be added in future versions.

The AES unit is attached to the chip interconnect bus as a peripheral module.
Communication with the processor happens through a set of control and status registers (CSRs).
This includes input/output data and key, as well as status and control information.
Future versions of the AES unit might include a separate interface through which a possible system key manager can provide the key without exposing it to the processor or other hosts attached to the system bus interconnect.


# Theory of Operations

The AES unit supports both encryption and decryption for AES-128/192/256 in ECB, CBC, CFB, OFB and CTR modes using a single, shared data path.
That is, it can either do encryption or decryption but not both at the same time.

The AES unit features a key expanding mechanism to generate the required round keys on-the-fly from a single initial key provided through the register interface.
This means the processor needs to provide just the initial encryption key to the AES unit via register interface.
The AES unit then uses this key to generate all round keys as they are needed in parallel to the actual encryption/decryption.
The benefits of this design compared to passing all round keys via register interface include:

- Reduced storage requirements and smaller circuit area: Instead of storing 15 128-bit round keys, only 3 256-bit key registers are required for AES-256:
  - one set of registers to which the processor writes the initial key, i.e., the start key for encryption,
  - one set of registers to hold the current full key, and
  - one set of registers to hold the full key of the last encryption round, i.e., the start key for decryption.
- Faster re-configuration and key switching: The core just needs to perform 8 write operations instead of 60 write operations for AES-256.

On-the-fly round-key generation comes however at the price of an initial delay whenever the key is changed by the processor before the AES unit can perform ECB/CBC **decryption** using this new key.
During this phase, the key expanding mechanism iteratively computes the start key for the decryption.
The duration of this delay phase corresponds to the latency required for encrypting one 16B block (i.e., 12/14/16 cycles for AES-128/192/256).
Once the start key for decryption has been computed, it is stored in a dedicated internal register for later use.
The AES unit can then switch between decryption and encryption without additional overhead.

For encryption or if the mode is set to CFB, OFB or CTR, there is no such initial delay upon changing the key.
If the next operation after a key switch is ECB or CBC **decryption**, the AES unit automatically initiates a key expansion using the key schedule first (to generate the start key for decryption, the actual data path remains idle during that phase).

The AES unit uses a status register to indicate to the processor when ready to receive the next input data block via the register interface.
While the AES unit is performing encryption/decryption of a data block, it is safe for the processor to provide the next input data block.
The AES unit automatically starts the encryption/decryption of the next data block once the previous encryption/decryption is finished and new input data is available.
The order in which the input registers are written does not matter.
Every input register must be written at least once for the AES unit to automatically start encryption/decryption.
This is the default behavior.
It can be disabled by setting the MANUAL_OPERATION bit in {{< regref "CTRL_SHADOWED" >}} to `1`.
In this case, the AES unit only starts the encryption/decryption once the START bit in {{< regref "TRIGGER" >}} is set to `1` (automatically cleared to `0` once the next encryption/decryption is started).

Similarly, the AES unit indicates via a status register when having new output data available to be read by the processor.
Also, there is a back-pressure mechanism for the output data.
If the AES unit wants to finish the encryption/decryption of a data block but the previous output data has not yet been read by the processor, the AES unit is stalled.
It hangs and does not drop data.
It only continues once the previous output data has been read and the corresponding registers can be safely overwritten.
The order in which the output registers are read does not matter.
Every output register must be read at least once for the AES unit to continue.
This is the default behavior.
It can be disabled by setting the MANUAL_OPERATION bit in {{< regref "CTRL_SHADOWED" >}} to `1`.
In this case, the AES unit never stalls and just overwrites previous output data, independent of whether it has been read or not.


## Block Diagram

This AES unit targets medium performance (\~1 cycle per round for the unmasked implementation).
High-speed, single-cycle operation for high-bandwidth data streaming is not required.

Therefore, the AES unit uses an iterative cipher core architecture with a 128-bit wide data path as shown in the figure below.
Note that for the sake of simplicity, the figure shows the unmasked implementation.
For details on the masked implementation of the cipher core refer to [Security Hardening below]({{< relref "#security-hardening" >}})).
Using an iterative architecture allows for a smaller circuit area at the cost of throughput.
Employing a 128-bit wide data path allows to achieve the latency requirements of 12/14/16 clock cycles per 16B data block in AES-128/192/256 mode in the unmasked implementation, respectively.

![AES unit block diagram (unmasked implementation) with shared data paths for encryption and decryption (using the Equivalent Inverse Cipher).](aes_block_diagram.svg)

Inside the cipher core, both the data paths for the actual cipher (left) and the round key generation (right) are shared between encryption and decryption.
Consequently, the blocks shown in the diagram always implement the forward and backward (inverse) version of the corresponding operation.
For example, SubBytes implements both SubBytes and InvSubBytes.

Besides the actual AES cipher core, the AES unit features a set of control and status registers (CSRs) accessible by the processor via TL-UL bus interface, and a counter module (used in CTR mode only).
This counter module implements the Standard Incrementing Function according to [Recommendation for Block Cipher Modes of Operation (Appendix B.1)](https://nvlpubs.nist.gov/nistpubs/Legacy/SP/nistspecialpublication800-38a.pdf) with a fixed parameter m = 128.
Note that for AES, parameter b = 128 and the counter increment is big-endian.
CFB mode is supported with a fixed parameter s = 128 (CFB-128).
Support for data segment sizes other than 128 bits would require a substantial amount of additional muxing resources and is thus not provided.
The initialization vector (IV) register and the register to hold the previous input data are used in CBC, CFB, OFB and CTR modes only.


## Hardware Interfaces

{{< incGenFromIpDesc "../data/aes.hjson" "hwcfg" >}}

The table below lists other signals of the AES unit.

Signal             | Direction        | Type                   | Description
-------------------|------------------|------------------------|---------------
`idle_o`           | `output`         | `logic`                | Idle indication signal for clock manager.
`lc_escalate_en_i` | `input`          | `lc_ctrl_pkg::lc_tx_t` | Life cycle escalation enable coming from [life cycle controller]({{< relref "hw/ip/lc_ctrl/doc" >}}). This signal moves the main controller FSM within the AES unit into the terminal error state. The AES unit needs to be reset.
`edn_o`            | `output`         | `edn_pkg::edn_req_t`   | Entropy request to [entropy distribution network (EDN)]({{< relref "hw/ip/edn/doc" >}}) for reseeding internal pseudo-random number generators (PRNGs) used for register clearing and masking.
`edn_i`            | `input`          | `edn_pkg::edn_rsp_t`   | [EDN]({{< relref "hw/ip/edn/doc" >}}) acknowledgment and entropy input for reseeding internal PRNGs.
`keymgr_key_i`     | `input`          | `keymgr_pgk::hw_key_req_t` | Key sideload request coming from [key manager]({{< relref "hw/ip/keymgr/doc" >}}).

Note that the `edn_o` and `edn_i` signals used to interface [EDN]({{< relref "hw/ip/edn/doc" >}}) follow a REQ/ACK protocol.
The entropy distributed by EDN is obtained from the [cryptographically secure random number generator (CSRNG)]({{< relref "hw/ip/csrng/doc" >}}).

## Design Details

This section discusses different design details of the AES module.


### Datapath Architecture and Operation

The AES unit implements the Equivalent Inverse Cipher described in the [AES specification](https://csrc.nist.gov/csrc/media/publications/fips/197/final/documents/fips-197.pdf).
This allows for more efficient cipher data path sharing between encryption/decryption as the operations are applied in the same order (less muxes, simpler control), but requires the round key during decryption to be transformed using an inverse MixColumns in all rounds except for the first and the last one.

This architectural choice targets at efficient cipher data path sharing and low area footprint.
Depending on the application scenario, other architectures might offer a more suitable area/performance tradeoff.
For example if only CFB, OFB or CTR modes are ever used, the inverse cipher is not used at all.
Moreover, if the key is changed extremely rarely (as for example in the case of bulk decryption), it may pay off to store all round keys instead of generating them on the fly.
Future versions of the AES unit might offer compile-time parameters to selectively instantiate the forward/inverse cipher part only to allow for dedicated encryption/decryption-only units.

All submodules in the data path are purely combinational.
The only sequential logic in the cipher and round key generation are the State, Full Key and Decryption Key registers.

The following description explains how the AES unit operates, i.e., how the operation of the AES cipher is mapped to the datapath architecture of the AES unit.
Phrases in italics apply to peculiarities of different block cipher modes.
For a general introduction into these cipher modes, refer to [Recommendation for Block Cipher Modes of Operation](https://nvlpubs.nist.gov/nistpubs/Legacy/SP/nistspecialpublication800-38a.pdf).

1. The configuration and initial key is provided to the AES unit via a set of control and status registers (CSRs) accessible by the processor via TL-UL bus interface.
   The processor must first provide the configuration to the {{< regref "CTRL_SHADOWED" >}} register.
   Then follows the initial key.
   Each key register must be written at least once.
   The order in which the registers are written does not matter.
1. _The processor provides the initialization vector (IV) or initial counter value to the four IV registers via TL-UL bus interface in CBC, CFB and OFB modes, or CTR mode, respectively.
   Each IV register must be written at least once.
   The order in which the registers are written does not matter.
   Note that while operating, the AES unit automatically updates the IV registers after having consumed the current IV value.
   Whenever a new message is started, the processor must provide the corresponding IV value via TL-UL bus interface.
   In ECB mode, no IV needs to be provided.
   The content of the IV registers is ignored in ECB mode._
1. The input data is provided to the AES unit via four CSRs.
   Each input register must be written at least once.
   The order in which the registers are written does not matter.
1. If new input data is available, the AES unit automatically starts encryption/decryption by performing the following actions.
    1. The AES unit loads initial state into the State register inside the cipher core.

       _Depending on the cipher mode, the initial state is a combination of input data as well as IV._
       _Note, if CBC decryption is performed, or if running in CFB, OFB or CTR mode, the input data is also registered (Data In Prev in the block diagram)._
    2. The initial key is loaded into the Full Key register inside the cipher core.

       _Note, if the ECB/CBC decryption is performed, the Full Key register is loaded with the value stored in the Decryption Key register._

    _Note, for the AES unit to automatically start in CBC, CFB, OFB or CTR mode, also the IV must be ready.
    The IV is ready if -- since the last IV update (either done by the processor or the AES unit itself) -- all IV registers have been written at least once or none of them.
    The AES unit will not automatically start the next encryption/decryption with a partially updated IV._

    By setting the MANUAL_OPERATION bit in {{< regref "CTRL_SHADOWED" >}} to `1`, the AES unit can be operated in manual mode.
    In manual mode, the AES unit starts encryption/decryption whenever the START bit in {{< regref "TRIGGER" >}} is set to `1`, irrespective of the status of the IV and input data registers.

1. Once the State and Full Key registers have been loaded, the AES cipher core starts the encryption/decryption by adding the first round key to the initial state (all blocks in both data paths are bypassed).
   The result is stored back in the State register.
1. Then, the AES cipher core performs 9/11/13 rounds of encryption/decryption when using a 128/192/256-bit key, respectively.
   In every round, the cipher data path performs the four following transformations.
   For more details, refer to the [AES specification](https://csrc.nist.gov/csrc/media/publications/fips/197/final/documents/fips-197.pdf).
    1. SubBytes Transformation: A non-linear byte substitution that operates independently on each byte of the state using a substitution table (S-Box).
    2. ShiftRows Transformation: The bytes of the last three rows of the state are cyclically shifted over different offsets.
    3. MixColumns Transformation: Each of the four columns of the state are considered as polynomials over GF(2^8) and individually multiplied with another fixed polynomial.
    4. AddRoundKey Transformation: The round key is XORed with the output of the MixColumns operation and stored back into the State register.
       The 128-bit round key itself is extracted from the current value in the Full Key register.

    In parallel, the full key used for the next round is computed on the fly using the key expand module.

    _If running in CTR mode, the counter module iteratively updates the IV in parallel to the cipher core performing encryption/decryption.
    Internally, the counter module uses one 16-bit counter, meaning it requires 8 clock cycles to increment the 128-bit counter value stored in the IV register.
    Since the counter value is used in the first round only, and since the encryption/decryption of a single block takes 12/14/16 cycles, the iterative counter implementation does not affect the throughput of the AES unit._
1. Finally, the AES cipher core performs the final encryption/decryption round in which the MixColumns operation is skipped.
   The output is forwarded to the output register in the CSRs but not stored back into the State register.
   The internal State register is cleared with pseudo-random data.

   _Depending on the cipher mode, the output of the final round is potentially XORed with either the value in the IV registers (CBC decryption) or the value stored in the previous input data register (CFB, OFB, CTR modes), before being forwarded to the output register in the CSRs.
   If running in CBC mode, the IV registers are updated with the output data (encryption) or the value stored in the previous input data register (decryption).
   If running in CFB or OFB mode, the IV registers are updated with the output data or the output of the final cipher round (before XORing with the previous input data), respectively._

Having separate registers for input, output and internal state prevents the extraction of intermediate state via TL-UL bus interface and allows to overlap reconfiguration with operation.
While the AES unit is performing encryption/decryption, the processor can safely write the next input data block into the CSRs or read the previous output data block from the CSRs.
The State register is internal to the AES unit and not exposed via the TL-UL bus interface.
If the AES unit wants to finish the encryption/decryption of an output data block but the previous one has not yet been read by the processor, the AES unit is stalled.
It hangs and does not drop data.
It only continues once the previous output data has been read and the corresponding registers can be safely overwritten.
The order in which the output registers are read does not matter.
Every output register must be read at least once for the AES unit to continue.
In contrast, the initial key, and control register can only be updated if the AES unit is idle, which eases design verification (DV).
Similarly, the initialization vector (IV) register can only be updated by the processor if the AES unit is idle.
If the AES unit is busy and running in CBC or CTR mode, the AES unit itself updates the IV register.

The cipher core architecture of the AES unit is derived from the architecture proposed by Satoh et al.: ["A compact Rijndael Hardware Architecture with S-Box Optimization"](https://link.springer.com/chapter/10.1007%2F3-540-45682-1_15).
The expected circuit area in a 110nm CMOS technology is in the order of 12 - 22 kGE (unmasked implementation, AES-128 only).
The expected circuit area of the entire AES unit with masking enabled is around 110 kGE.

For a description of the various sub modules, see the following sections.


### SubBytes / S-Box

The SubBytes operation is a non-linear byte substitution that operates independently on each byte of the state using a substitution table (S-Box).
It is both used for the cipher data path and the key expand data path.
In total, the AES unit instantiates 20 S-Boxes in parallel (16 for SubBytes, 4 for KeyExpand), each having 8-bit input and output.
In combination with the 128-bit wide data path, this allows to perform one AES round per iteration.

The design of this S-Box and its inverse can have a big impact on circuit area, timing critical path, robustness and power leakage, and is itself its own research topic.

The S-Boxes are decoupled from the rest of the AES unit with a handshake protocol, allowing them to be easily replaced by different implementations if required.
The AES unit comes with the following S-Box implementations that can be selected by a compile-time Verilog parameter:
- Domain-oriented masking (DOM) S-Box: default, see [Gross et al.: "Domain-Oriented Masking: Compact Masked Hardware Implementations with Arbitrary Protection Order"](https://eprint.iacr.org/2016/486.pdf)
- Masked Canright S-Box: provided for reference, usage discouraged, a version w/ and w/o mask re-use is provided, see [Canright and Batina: "A very compact "perfectly masked" S-Box for AES (corrected)"](https://eprint.iacr.org/2009/011.pdf)
- Canright S-Box: only use when disabling masking, recommended when targeting ASIC implementation, see [Canright: "A very compact Rijndael S-Box"](https://hdl.handle.net/10945/25608)
- LUT-based S-Box: only use when disabling masking, recommended when targeting FPGA implementation

The DOM S-Box has a latency of 5 clock cycles.
All other implementations are fully combinational (one S-Box evaluation every clock cycle).
See also [Security Hardening below.]({{< relref "#1st-order-masking-of-the-cipher-core" >}})

### ShiftRows

The ShiftRows operation simply performs a cyclic shift of Rows 1, 2 and 3 of the state matrix.
Consequently, it can be implemented using 3\*4 32-bit 2-input muxes (encryption/decryption).


### MixColumns

Each of the four columns of the state are considered as polynomials over GF(2^8) and individually multiplied with another fixed polynomial.
The whole operation can be implemented using 36 2-input XORs and 16 4-input XORs (all 8-bit), 8 2-input muxes (8-bit), as well as 78 2-input and 24 3-input XOR gates.


### KeyExpand

The key expand module (KEM) integrated in the AES unit is responsible for generating the various round keys from the initial key for both encryption and decryption.
The KEM generates the next 128/192/256-bit full key in parallel to the actual encryption/decryption based on the current full key or the initial key (for the first encryption round).
The actual 128-bit round key is then extracted from this full key.

Generating the keys on-the-fly allows for lower storage requirements and smaller circuit area but comes at the price of an initial delay before doing ECB/CBC **decryption** whenever the key is changed.
During this phase, the KEM cycles through all full keys to obtain the start key for decryption (equals the key for final round of encryption).
The duration of this delay phase corresponds to the latency required for encrypting one 16B block.
During this initial phase, the cipher data path is kept idle.

The timing diagram below visualizes this process.

{{< wavejson >}}
{
  signal: [
    {    name: 'clk',       wave: 'p........|.......'},
    ['TL-UL IF',
      {  name: 'write',     wave: '01...0...|.......'},
      {  name: 'addr',      wave: 'x2345xxxx|xxxxxxx', data: 'K0 K1 K2 K3'},
      {  name: 'wdata',     wave: 'x2345xxxx|xxxxxxx', data: 'K0 K1 K2 K3'},
    ],
    {},
    ['AES Unit',
      {  name: 'Config op', wave: 'x4...............', data: 'DECRYPT'},
      {  name: 'AES op',    wave: '2........|.4.....', data: 'IDLE DECRYPT'},
      {  name: 'KEM op',    wave: '2....3...|.4.....', data: 'IDLE ENCRYPT DECRYPT'},
      {  name: 'round',     wave: 'xxxxx2.22|22.2222', data: '0 1 2 9 0 1 2 3 4'},
      {  name: 'key_init',  wave: 'xxxx5....|.......', data: 'K0-3'},
      {  name: 'key_full',  wave: 'xxxxx5222|4.22222', data: 'K0-3 f(K) f(K) f(K) K0-3\' f(K) f(K) f(K) f(K) f(K)'},
      {  name: 'key_dec',   wave: 'xxxxxxxxx|4......', data: 'K0-3\''},
    ]
  ]
}
{{< /wavejson >}}

The AES unit is configured to do decryption (`Config op` = DECRYPT).
Once the new key has been provided via the control and status registers (top), this new key is loaded into the Full Key register (`key_full` = K0-3) and the KEM starts performing encryption (`KEM op`=ENCRYPT).
The cipher data path remains idle (`AES op`=IDLE).
In every round, the value in `key_full` is updated.
After 10 encryption rounds, the value in `key_full` equals the start key for decryption.
This value is stored into the Decryption Key register (`key_dec` = K0-3' at the very bottom).
Now the AES unit can switch between encryption/decryption without overhead as both the start key for encryption (`key_init`) and decryption (`key_dec`) can be loaded into `full_key`.

For details on the KeyExpand operation refer to the [AES specification, Section 5.2](https://csrc.nist.gov/csrc/media/publications/fips/197/final/documents/fips-197.pdf).

Key expanding is the only operation in the AES unit for which the functionality depends on the selected key length.
Having a KEM that supports 128-bit key expansion, support for the 256-bit mode can be added at low overhead.
In contrast, the 192-bit mode requires much larger muxes.
Support for this mode is thus optional and can be enabled/disabled via a design-time parameter.

Once we have cost estimates in terms of gate count increase for 192-bit mode, we can decide on whether or not to use it in OpenTitan.
Typically, systems requiring security above AES-128 go directly for AES-256.

### System Key-Manager Interface

By default, the AES unit is controlled entirely by the processor.
The processor writes both input data as well as the initial key to dedicated registers via the system bus interconnect.

Alternatively, the processor can configure the AES unit to use an initial key provided by the [key manager]({{< relref "hw/ip/keymgr/doc" >}}) via key sideload interface without exposing the key to the processor or other hosts attached to the system bus interconnect.
To this end, the processor has to set the SIDELOAD bit in {{< regref "CTRL_SHADOWED" >}} to `1`.
Any write operations of the processor to the Initial Key registers {{< regref "KEY_SHARE0_0" >}} - {{< regref "KEY_SHARE1_7" >}} are then ignored.
In normal/automatic mode, the AES unit only starts encryption/decryption if the sideload key is marked as valid.
To update the sideload key, the processor has to 1) wait for the AES unit to become idle, 2) wait for the key manager to update the sideload key and assert the valid signal, and 3) write to the {{< regref "CTRL_SHADOWED" >}} register to start a new message.
After using a sideload key, the processor has to trigger the clearing of all key registers inside the AES unit (see [De-Initialization]({{< relref "#de-initialization" >}}) below).


# Security Hardening

The AES unit employs different means at architectural, micro-architectural and physical levels for security hardening against side-channel analysis and fault injection.

## Side-Channel Analysis

To aggravate side-channel analysis (SCA), the AES unit implements the following countermeasures.

### 1st-order Masking of the Cipher Core

The AES unit employs 1st-order masking of the AES cipher core.
More precisely, both the cipher and the key expand data path use two shares.
As shown in the block diagram below, the width of all registers and data paths basically doubles.

![Block diagram of the masked AES cipher core.](aes_block_diagram_cipher_core_masked.svg)

The initial key is provided in two shares via the register interface.
The input data is provided in unmasked form and masked outside of the cipher core to obtain the two shares of the initial state.
The pseudo-random data (PRD) required for masking the input data is provided by the pseudo-random number generator (PRNG) of the cipher core.
Similarly, the two shares of the output state are combined outside the cipher core to obtain the output data.

The same PRNG also generates the fresh randomness required by the masked SubBytes (16 masked S-Boxes) and the masked KeyExpand (4 masked S-Boxes).
The masking scheme selected for the S-Box can have a high impact on SCA resistance, circuit area, number of PRD bits consumed per cycle and per S-Box evaluation, and throughput.
The selection of the masked S-Box implementation can be controlled via compile-time Verilog parameter.
By default, the AES unit uses domain-oriented masking (DOM) for the S-Boxes as proposed by [Gross et al.: "Domain-Oriented Masking: Compact Masked Hardware Implementations with Arbitrary Protection Order".](https://eprint.iacr.org/2016/486.pdf)
The provided implementation has a latency of 5 clock cycles per S-Box evaluation.
As a result, the overall latency for processing a 16-byte data block increases from 12/14/16 to 56/66/72 clock cycles in AES-128/192/256 mode, respectively.
The provided implementation further forwards partial, intermediate results among DOM S-Box instances for remasking purposes.
This allows to reduce circuit area related to generating, buffering and applying PRD without impacting SCA resistance.
Alternatively, the two original versions of the masked Canright S-Box can be chosen as proposed by [Canright and Batina: "A very compact "perfectly masked" S-Box for AES (corrected)".](https://eprint.iacr.org/2009/011.pdf)
These are fully combinational (one S-Box evaluation every cycle) and have lower area footprint, but they are significantly less resistant to SCA.
They are mainly included for reference but their usage is discouraged due to potential vulnerabilities to the correlation-enhanced collision attack as described by [Moradi et al.: "Correlation-Enhanced Power Analysis Collision Attack".](https://eprint.iacr.org/2010/297.pdf)

The masking PRNG is reseeded with fresh entropy via [EDN]({{< relref "hw/ip/edn/doc" >}}) automatically 1) whenever a new key is provided (see {{< regref "CTRL_AUX_SHADOWED.KEY_TOUCH_FORCES_RESEED" >}}) and 2) based on a block counter.
The rate at which this block counter initiates automatic reseed operations can be configured via {{< regref "CTRL_SHADOWED.PRNG_RESEED_RATE" >}}.
In addition software can manually initiate a reseed operation via {{< regref "TRIGGER.PRNG_RESEED" >}}.

Note that the masking can be enabled/disabled via compile-time Verilog parameter.
It may be acceptable to disable the masking when using the AES cipher core for random number generation e.g. inside [CSRNG.]({{< relref "hw/ip/csrng/doc" >}})
When disabling the masking, also an unmasked S-Box implementation needs to be selected using the corresponding compile-time Verilog parameter.
When disabling masking, it is recommended to use the unmasked Canright or LUT S-Box implementation for ASIC or FPGA targets, respectively.
Both are fully combinational and allow for one S-Box evaluation every clock cycle.

It's worth noting that since input/output data are provided/retrieved via register interface in unmasked form, the AES unit should not be used to form an identity ladder where the output of one AES operation is used to form the key for the next AES operation in the ladder.
In OpenTitan, the [Keccak Message Authentication Code (KMAC) unit]({{< relref "hw/ip/kmac/doc" >}}) is used for that purpose.

### Fully-Parallel Data Path

Any 1st-order masking scheme primarily protects against 1st-order SCA.
Vulnerabilities against higher-order SCA might still be present.
A common technique to aggravate higher-order attacks is to increase the noise in the system e.g. by leveraging parallel architectures.
To this end, the AES cipher core uses a 128-bit parallel data path with a total of up to 20 S-Boxes (16 inside SubBytes, 4 inside KeyExpand) that are evaluated in parallel.

Besides more noise for increased resistance against higher-order SCA, the fully-parallel architecture also enables for higher performance and flexibility.
It allows users to seamlessly switch out the S-Box implementation in order to experiment with different masking schemes.
To interface the data paths with the S-Boxes, a handshake protocol is used.

### Note on Reset vs. Non-Reset Flip-Flops

The choice of flip-flop type for registering sensitive assets such as keys can have implications on the vulnerability against e.g. combined reset glitch attacks and SCA.
Following the [OpenTitan non-reset vs. reset flops rationale](https://github.com/lowRISC/opentitan/issues/2603), the following observations can be made:
- If masking is enabled, key and state values are stored in two shares inside the AES unit.
  Neither the Hamming weights of the individual shares nor the summed Hamming weight are proportional to the Hamming weight of the secret asset.
- Input/output data and IV values are (currently) not stored in multiple shares but these are less critical as they are used only once.
  Further, they are stored in banks of 32 bits leaving a larger hypothesis space compared to when glitching e.g. an 8-bit register into reset.
  In addition, they could potentially also be extracted when being transferred over the TL-UL bus interface.

For this reason, the AES unit uses reset flops only.
However, all major key and data registers are cleared with pseudo-random data upon reset.

### Clearing Registers with Pseudo-Random Data

Upon reset or if initiated by software, all major key and data registers inside the AES module are cleared with pseudo-random data (PRD).
This helps to reduce SCA leakage when both writing these registers for reconfiguration and when clearing the registers after use.

In addition, the state registers inside the cipher core are cleared with PRD during the last round of every encryption/decryption.
This prevents Hamming distance leakage between the states of the last two rounds as well as between output and input data.

## Fault Injection

Fault injection (FI) attacks can be distinguished based on the FI target.

### Control Path

In cryptographic devices, fault attacks on the control path usually aim to disturb the control flow in a way to facilitate SCA or other attacks.
Example targets for AES include: switch to less secure mode of operation (ECB), keep processing the same input data, reduce the number of rounds/early termination, skip particular rounds, skip individual operations in a round.

To protect against FI attacks on the control path, the AES unit implements the following countermeasures.

- Shadowed Control Register:
  The main control register is implemented as a shadow register.
  This means software has to perform two subsequent write operations to perform an update.
  Internally, a shadow copy is used that is constantly compared with the actual register.
  For further details, refer to the [Register Tool documentation.]({{< relref "doc/rm/register_tool#shadow-registers" >}})

- Sparse encodings of FSM states:
  All FSMs inside the AES unit use sparse state encodings.

- Sparse encodings for mux selector signals:
  All main muxes use sparsely encoded selector signals.

- Sparse encodings for handshake and other important control signals.

- Multi-rail control logic:
  All FSMs inside the AES unit are implemented using multiple independent and redundant logic rails.
  Every rail evaluates and drives exactly one bit of sparsely encoded handshake or other important control signals.
  The outputs of the different rails are constantly compared to detect potential faults.
  The number of logic rails can be scaled up by means of relatively easy RTL modifications.
  By default, three independent logic rails are used.

- Hardened round counter:
  Similar to the cipher core FSM, the internal round counter is protected against FI through a multi-rail implementation.
  The outputs of the different rails are constantly compared to detect potential faults in the round counter.

If any of these countermeasures detects a fault, a fatal alert is triggered, the internal FSMs go into a terminal error state, the AES unit does not release further data and locks up until reset.
Since the AES unit has no ability to reset itself, a system-supplied reset is required before the AES unit can become operational again.
Such a condition is reported in {{< regref "STATUS.ALERT_FATAL_FAULT" >}}.
Details on where the fault has been detected are not provided.

### Data Path

The aim of fault attacks on the data path is typically to extract information on the key by means of statistical analysis.
The current version of the AES unit does not employ countermeasures against such attacks, but future versions most likely will.


# Programmers Guide

This section discusses how software can interface with the AES unit.


## Clear upon Reset

Upon reset, the AES unit will first reseed the internal PRNGs for register clearing and masking via EDN, and then clear all key, IV and data registers with pseudo-random data.
Only after this sequence has finished, the unit becomes idle (indicated in {{< regref "STATUS.IDLE" >}}).
The AES unit is then ready for software initialization.
Note that at this point, the key, IV and data registers' values can no longer be expected to match the reset values.


## Initialization

Before initialization, software must ensure that the AES unit is idle by checking {{< regref "STATUS.IDLE" >}}.
If the AES unit is not idle, write operations to {{< regref "CTRL_SHADOWED" >}}, the Initial Key registers {{< regref "KEY_SHARE0_0" >}} - {{< regref "KEY_SHARE1_7" >}} and initialization vector (IV) registers {{< regref "IV_0" >}} - {{< regref "IV_3" >}} are ignored.

To initialize the AES unit, software must first provide the configuration to the {{< regref "CTRL_SHADOWED" >}} register.
Since writing this register may initiate the reseeding of the internal PRNGs, software must check that the AES unit is idle before providing the initial key.
Then software must write the initial key to the Initial Key registers {{< regref "KEY_SHARE0_0" >}} - {{< regref "KEY_SHARE1_7" >}}.
The key is provided in two shares:
The first share is written to {{< regref "KEY_SHARE0_0" >}} - {{< regref "KEY_SHARE0_7" >}} and the second share is written to {{< regref "KEY_SHARE1_0" >}} - {{< regref "KEY_SHARE1_7" >}}.
The actual initial key used for encryption corresponds to the value obtained by XORing {{< regref "KEY_SHARE0_0" >}} - {{< regref "KEY_SHARE0_7" >}} with {{< regref "KEY_SHARE1_0" >}} - {{< regref "KEY_SHARE1_7" >}}.
Note that all registers are little-endian.
The key length is configured using the KEY_LEN field of {{< regref "CTRL_SHADOWED" >}}.
Independent of the selected key length, software must always write all 8 32-bit registers of both shares.
Each register must be written at least once.
The order in which the key registers are written does not matter.
Anything can be written to the unused key registers of both shares, however, random data is preferred.
For AES-128 ,the actual initial key used for encryption is formed by XORing {{< regref "KEY_SHARE0_0" >}} - {{< regref "KEY_SHARE0_3" >}} with {{< regref "KEY_SHARE1_0" >}} - {{< regref "KEY_SHARE1_3" >}}.
For AES-192, the actual initial key used for encryption is formed by XORing {{< regref "KEY_SHARE0_0" >}} - {{< regref "KEY_SHARE0_5" >}} with {{< regref "KEY_SHARE1_0" >}} - {{< regref "KEY_SHARE1_5" >}}.

If running in CBC, CFB, OFB or CTR mode, software must also write the IV registers {{< regref "IV_0" >}} - {{< regref "IV_3" >}}.
Since providing the initial key initiate the reseeding of the internal PRNGs, software must check that the AES unit is idle before writing the IV registers.
These registers are little-endian, but the increment of the IV in CTR mode is big-endian (see [Recommendation for Block Cipher Modes of Operation](https://nvlpubs.nist.gov/nistpubs/Legacy/SP/nistspecialpublication800-38a.pdf)).
Each IV register must be written at least once.
The order in which these registers are written does not matter.
Note that the AES unit automatically updates the IV registers when running in CBC, CFB, OFB or CTR mode (after having consumed the current IV value).
To start the encryption/decryption of a new message, software must wait for the AES unit to become idle and then provide new values to the IV registers.

## Block Operation

For block operation, software must initialize the AES unit as described in the previous section.
In particular, the AES unit must be configured to run in normal/automatic mode.
This is indicated by the MANUAL_OPERATION bit in {{< regref "CTRL_SHADOWED" >}} reading as `0`.
It ensures that the AES unit:
1. Automatically starts encryption/decryption when new input data is available.
1. Does not overwrite previous output data that has not yet been read by the processor.

Then, software must:
1. Ensure that the INPUT_READY bit in {{< regref "STATUS" >}} is `1`.
1. Write Input Data Block `0` to the Input Data registers {{< regref "DATA_IN_0" >}} - {{< regref "DATA_IN_3" >}}.
   Each register must be written at least once.
   The order in which these registers are written does not matter.
1. Wait for the INPUT_READY bit in {{< regref "STATUS" >}} to become `1`, i.e. wait for the AES unit to load Input Data Block `0` into the internal state register and start operation.
1. Write Input Data Block `1` to the Input Data registers.

Then for every Data Block `I=0,..,N-3`, software must:
1. Wait for the OUTPUT_VALID bit in {{< regref "STATUS" >}} to become `1`, i.e., wait for the AES unit to finish encryption/decryption of Block `I`.
   The AES unit then directly starts processing the previously input block `I+1`
2. Read Output Data Block `I` from the Output Data registers {{< regref "DATA_OUT_0" >}} - {{< regref "DATA_OUT_3" >}}.
   Each register must be read at least once.
   The order in which these registers are read does not matter.
3. Write Input Data Block `I+2` into the Input Data register.
   There is no need to explicitly check INPUT_READY as in the same cycle OUTPUT_VALID becomes `1`, the current input is loaded in (meaning INPUT_READY becomes `1` one cycle later).

Once all blocks have been input, the final data blocks `I=N-2,N-1` must be read out:
1. Wait for the OUTPUT_VALID bit in {{< regref "STATUS" >}} to become `1`, i.e., wait for the AES unit to finish encryption/decryption of Block `I`.
2. Read Output Data Block `I` from the Output Data register.

Note that interrupts are not provided, the latency of the AES unit is such that they are of little utility.

The code snippet below shows how to perform block operation.

```c
  // Enable autostart, disable overwriting of previous output data. Note the control register is
  // shadowed and thus needs to be written twice.
  uint32_t aes_ctrl_val =
      (op & AES_CTRL_SHADOWED_OPERATION_MASK) << AES_CTRL_SHADOWED_OPERATION_OFFSET |
      (mode & AES_CTRL_SHADOWED_MODE_MASK) << AES_CTRL_SHADOWED_MODE_OFFSET |
      (key_len & AES_CTRL_SHADOWED_KEY_LEN_MASK) << AES_CTRL_SHADOWED_KEY_LEN_OFFSET |
      0x0 << AES_CTRL_SHADOWED_MANUAL_OPERATION_OFFSET;
  REG32(AES_CTRL_SHADOWED(0)) = aes_ctrl_val;
  REG32(AES_CTRL_SHADOWED(0)) = aes_ctrl_val;

  // Write key - Note: All registers are little-endian.
  for (int j = 0; j < 8; j++) {
    REG32(AES_KEY_SHARE0_0(0) + j * 4) = key_share0[j];
    REG32(AES_KEY_SHARE1_0(0) + j * 4) = key_share1[j];
  }

  // Write IV.
  for (int j = 0; j < 4; j++) {
    REG32(AES_IV_0(0) + j * 4) = iv[j];
  }

  // Write Input Data Block 0.
  for (int j = 0; j < 4; j++) {
    REG32(AES_DATA_IN_0(0) + j * 4) = input_data[j];
  }

  // Wait for INPUT_READY bit
  while (!((REG32(AES_STATUS(0)) >> AES_STATUS_INPUT_READY) & 0x1)) {
  }

  // Write Input Data Block 1
  for (int j = 0; j < 4; j++) {
    REG32(AES_DATA_IN_0(0) + j * 4) = input_data[j + 4];
  }

  // For Data Block I=0,...,N-1
  for (int i = 0; i < N; i++) {

    // Wait for OUTPUT_VALID bit
    while (!((REG32(AES_STATUS(0)) >> AES_STATUS_OUTPUT_VALID) & 0x1)) {
    }

    // Read Output Data Block I
    for (int j = 0; j < 4; j++) {
      output_data[j + i * 4] = REG32(AES_DATA_OUT_0(0) + j * 4);
    }

    // Write Input Data Block I+2 - For I=0,...,N-3 only.
    if (i < N - 2) {
      for (int j = 0; j < 4; j++) {
        REG32(AES_DATA_IN_0(0) + j * 4) = input_data[j + 4 * (i + 2)];
      }
    }
  }

```


## Padding

For the AES unit to automatically start encryption/decryption of the next data block, software is required to always update all four Input Data registers {{< regref "DATA_IN_0" >}} - {{< regref "DATA_IN_3" >}} and read all four Output Data registers {{< regref "DATA_OUT_0" >}} - {{< regref "DATA_OUT_3" >}}.
This is also true if the AES unit is operated in OFB or CTR mode, i.e., if the plaintext/ciphertext not necessarily needs to be a multiple of the block size (for more details refer to Appendix A of [Recommendation for Block Cipher Modes of Operation](https://nvlpubs.nist.gov/nistpubs/Legacy/SP/nistspecialpublication800-38a.pdf)).

In the case that the plaintext/ciphertext is not a multiple of the block size and the AES unit is operated in OFB or CTR mode, software can employ any form of padding for the input data of the last message block as the padding bits do not have an effect on the actual message bits.
It is recommended that software discards the padding bits after reading the output data.


## De-Initialization

After finishing operation, software must:
1. Disable the AES unit to no longer automatically start encryption/decryption by setting the MANUAL_OPERATION bit in {{< regref "CTRL_SHADOWED" >}} to `1`.
1. Clear all key registers, IV registers as well as the Input Data and the Output Data registers with pseudo-random data by setting the KEY_IV_DATA_IN_CLEAR and DATA_OUT_CLEAR bits in {{< regref "TRIGGER" >}} to `1`.

The code snippet below shows how to perform this task.

```c
  // Disable autostart. Note the control register is shadowed and thus needs to be written twice.
  uint32_t aes_ctrl_val = 0x1 << AES_CTRL_SHADOWED_MANUAL_OPERATION;
  REG32(AES_CTRL_SHADOWED(0)) = aes_ctrl_val;
  REG32(AES_CTRL_SHADOWED(0)) = aes_ctrl_val;

  // Clear all key, IV, Input Data and Output Data registers.
  REG32(AES_TRIGGER(0)) =
      (0x1 << AES_TRIGGER_KEY_IV_DATA_IN_CLEAR) |
      (0x1 << AES_TRIGGER_DATA_OUT_CLEAR);
```

## Device Interface Functions (DIFs)

{{< dif_listing "sw/device/lib/dif/dif_aes.h" >}}

## Register Table

The AES unit uses 8 and 2x4 separate write-only registers for the initial key, initialization vector, and input data, as well as 4 separate read-only registers for the output data.
All registers are little-endian.
Compared to first-in, first-out (FIFO) interfaces, having separate registers has a couple of advantages:

- Supported out-of-the-box by the register tool (the FIFO would have to be implemented separately).
- Usability: critical corner cases where software updates input data or the key partially only are easier to avoid using separate registers and the `hwqe`-signals provided by the Register Tool.
- Easier interaction with DMA engines

Also, using a FIFO interface for something that is not actually FIFO (internally, 16B of input/output data are consumed/produced at once) is less natural.

For a detailed overview of the register tool, please refer to the [Register Tool documentation.]({{< relref "doc/rm/register_tool" >}})

{{< incGenFromIpDesc "../data/aes.hjson" "registers" >}}
