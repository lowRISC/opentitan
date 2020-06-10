---
title: "ENTROPY_SRC HWIP Technical Specification"
---

# Overview

This document specifies ENTROPY_SRC hardware IP functionality.
This module conforms to the [Comportable guideline for peripheral functionality.]({{< relref "doc/rm/comportability_specification" >}})


## Features

- This revision supports a LFSR (linear feedback shift register) digital source, and provides an interface to an external rng (random noise generator) source.
The LFSR is used as a digital, pseudo-random type of entropy source, while the rng external source is a true entropy source.
A noise source and its relation to an entropy source are defined by [SP 800-90B](https://csrc.nist.gov/publications/detail/sp/800-90b/final).
- A set of registers is provided for firmware to manage and obtain entropy bits.
- The set of registers is designed such that firmware can select between a digital or an rng entropy source.
- Interrupts are supported:
  - Entropy bits are available for firmware consumption.
  - The external rng entropy source is available.
  - The internal health tests have detected a repetitive count test fail.
  - The internal health tests have detected an adaptive proportion test fail.
  - An internal FIFO error has occurred.
- Two health checks that are defined by SP 800-90B are performed by this revision:  Repetition Count and Adaptive Proportion tests.
- No alerts are supported by this revision.


## Description

This IP block provides an entropy source that is part of a larger solution to generate true random numbers (a TRNG mechanism).
The general solution for TRNG relies on either hardware or firmware to implement this function, depending which functions are enabled by firmware or e-fuses.
For purposes of reference in this document, the NIST term "noise" will be synonymous with the term "entropy".
Likewise, no conditioning function will be performed in this block.
For the generation of entropy, this block provides the entropy bits needed for the entropy source solution as required by the RNG mechanism.

At a high-level, this ENTROPY_SRC block, when enabled, will continuously collect entropy bits from the entropy source into a FIFO that can be read from the TLUL bus, or sent out through a hardware interface.
The rng source will generate a relative slow set of bit streams, in the tens of kilohertz range.
The digital source can be programmed to be faster, or much slower if desired.
A digital source rate of flexiable speed might be useful in demonstrating how the downstream applications use the entropy.

Once the threshold has been reached for collected entropy bits, the firmware has two options of notification: an interrupt, or polling.
The `es_entropy_valid` bit will be set when the {{< regref "ES_THRESH" >}} register value is equal or less than the number of elements in the TLUL FIFO.
Optionally, an interrupt may be a better use of CPU cycles.
For the hardware interface, entropy bits will be transferred whenever the downstream consumer is ready to receive them.

## Compatibility
This IP block does not have any direct hardware compatibility requirements.
The firmware routines, as described by SP 800-90B, must be supported.
However, as long as the function provided by the register set supports all of the call parameters, any compatibility requirements will be met.

# Theory of Operations

As already described, this IP block will collect bits of entropy for firmware or hardware consumption.
This revision supports both an LFSR for the digital implementation, and an external interface for the rng implementation.
For the LRSR implementation, any polynomial may be used so long as it is primitive in Galois Field of order 2, or GF(2).
However, preference should be given to polynomials with the fewest number of terms.

The first step is initialization and enabling.
Before setting the `ENABLE` field, the LFSR seed input should be initialized, using the {{< regref "ES_SEED" >}} register.
The {{< regref "ES_SEED" >}} register will transfer its value according to the initialization sequence.
After the block is enabled and initialized, entropy bits will be collected up indefinitely until disabled.
If rng mode is desired, the `RNG_SRC_EN` bit can be set at the same time as the `ENABLE` field can be set to enable rng mode.

It is assumed that any entropy source will drop bits.
This means that the FIFO used to collect up the entropy bits will fill, and until the firmware or hardware starts pulling out bits, continuously generated entropy source bits may be dropped from usage.
The process of filling and draining the FIFOs is the same, independent of what speed the entropy generation rate is at.

Once the `es_entropy_valid` status bit is set, the firmware will read the {{< regref "ES_ENTROPY" >}} register as many times as needed to get the required entropy bits, typically 128 bits or 256 bits at a time.
For ease of firmware operation, the status bit does not need to be reset.
A read of the {{< regref "ES_THRESH" >}} register could be done to verify how many entries are in the FIFO at the current time.
The {{< regref "ES_THRESH" >}} register will determine when the status bit is set, or when the interrupt will assert if enabled.
For this revision, this same {{< regref "ES_THRESH" >}} register has a range of between 1 and 4 entries in the TLUL FIFO.

For hardware consumption of entropy, if the HWIF FIFO is not empty, and the entropy consuming hardware is ready, then entropy bits will be transferred over the hardware entropy interface.

Health tests, when enabled in the {{< regref "ES_CONF" >}} register, will run continuously.
Two tests are implemented in hardware, the repetition count test (RCT), and the adaptive proportion test (APT).

There are four health test blocks, one per inbound rng bus bit.
Each health test block works independently from one another.
The checks are done on the serial stream input, and an optional feature allows for passing entropy from a single bit stream source.
Once the streams have passed the health tests, it becomes available for downstream consumption.
If the health tests ever fail, the ES FIFO is prevented from receiving additional entropy bits up.
The entropy health tests will continue until a clean stream is detected, at which time the ES FIFO will start collecting bits again.
The {{< regref "ES_RCT_HEALTH" >}} register and the  {{< regref "ES_APT_HEALTH" >}} register set the cutoff limits for the health tests.

The above process will be repeated for as long as entropy bits are to be collected.
At any time, the enable bit can be cleared, and the entropy generation will halt immediately.


## Block Diagram

![ENTROPY_SRC Block Diagram](entsrc_blk_diag.svg)

## Hardware Interfaces

{{< hwcfg "hw/ip/entropy_src/data/entropy_src.hjson" >}}

## Design Details

### Initialization

After power-up, the ENTROPY_SRC block is disabled.
In this state, the seed register will continuously be loaded into the LFSR.
The seed register can be written without restriction, regardless of any state of any control bits.

A configuration/control register locking function is performed by the {{< regref "ES_REGEN" >}} register.
Clearing the bit in this register will prevent future modification of the {{< regref "ES_CONF" >}} register or the  {{< regref "ES_SEED" >}} by firmware.

The {{< regref "ES_SEED" >}} register can be updated at any time while the digital source FIFO is in operational mode.
As long as the update sequence is followed by firmware, there will be no timing hazards when accessing these registers by the firmware.

### Entropy Processing

When enabled, the ENTROPY_SRC block will generate entropy bits continuously.
The `es_entropy_valid` bit signal to the firmware when entropy bits should read from the {{< regref "ES_ENTROPY" >}} register.
While the firmware is reading the TLUL FIFO, additional entropy bits could be captured by the TLUL FIFO as long as the TLUL FIFO is not full.
The firmware will do 32-bit register reads of the {{< regref "ES_ENTROPY" >}} register to retrieve the entropy bits.
Each read will automatically pop an entry off the head of the TLUL FIFO.
New entropy bits can enter the TLUL FIFO at the tail concurrently.

The hardware entropy interface will move entropy bits out of the HWIF FIFO when it is not empty and the downstream hardware is ready.
The HWIF FIFO has lower priority than the TLUL FIFO, but is expected to have higher bandwidth demands.
Because of this, higher priority is given to the TLUL FIFO so that it does not starve when the hardware entropy interface is consuming a high level of entropy bits.

The {{< regref "ES_THRESH" >}} register is used to set the point of notification to the firmware.
Notification can be either by polling or by an interrupt.
For debug, the {{< regref "ES_FDEPTHST" >}} register can be read to find out the current state of the TLUL FIFO at any time.

An additional feature is the {{< regref "ES_RATE" >}} register.
The purpose of this register is to simulate faster or slower entropy generation sources when is digial source mode.
This will aid firmware design and debug when trying to handle all entropy source types and rates.
When in rng mode, this register must exactly match the sample rate required by the rng source, expected to be in the range of about 25 to 50 kilohertz.

### Interrupts

The ENTROPY_SRC module has several interrupts: `es_entropy_valid`, `es_rng_src_ok`, es_rct_failed, es_apt_failed`, and `es_fifo_err`.

The `es_entropy_valid` interrupt should be used when a entropy source has been implemented that is relatively slow.

The `es_rng_src_ok` interrupt should be used when rng entropy mode has been selected.
Once the external entropy source is operational, this interrupt will be triggered.

The `es_rct_failed` interrupt will trigger when the internal health test fails the repetitive count test.

The `es_apt_failed` interrupt will trigger when the internal health test fails the adaptive proportion test.

The `es_fifo_err` interrupt will fire when a non-rng FIFO has a malfunction.
The conditions that cause this to happen are either when there is a push to a full FIFO or a pull from an empty FIFO.

### TLUL FIFO Operational Sequence
The following waveform shows an example of how the entropy source is collected into the TLUL FIFO.
In this example, the TLUL FIFO parameter is fixed to a depth of 4. The {{< regref "ES_THRESH" >}} register is set to a value of 2, and will trigger an interrupt when the FIFO has met this value.
The FIFO in this example will fill quickly, then will drain as the firmware reads the {{< regref "ES_ENTROPY" >}} register. As the entropy bits are read out, new entropy bits, if available and valid,  will immediately enter the FIFO.


{{< wavejson >}}
{signal: [
   {name: 'clk'                 , wave: 'p.......|............'},
   {name: 'es_enable'           , wave: '01......|............'},
   {name: 'fifo_push_capt_entropy', wave: '0..1...0|.10.10.10.10', data: ['ph0','ph1','ph2','ph3']},
   {name: 'entropy_bits'          , wave: 'x..3453x|.4x.5x.3x.4x', data: ['es0','es1','es2','es3','es4','es5','es6','es7']},
   {name: 'fifo_full'           , wave: '0......1|.01.01.01.01'},
   {name: 'fifo_empty'          , wave: '1..0....|............'},
   {name: 'fifo_pop_read_entropy' , wave: '0.......|10.10.10.10.'},
   {name: 'threshold reg'       , wave: '4.......|............', data: ['2']},
   {name: 'interrupt/status'    , wave: '0....1..|............'},
 {},
]}{{< /wavejson >}}


### Entropy Source Hardware Interface
The following waveform shows an example of how the entropy source hardware interface works, which is much like a FIFO.


{{< wavejson >}}
{signal: [
   {name: 'clk'                , wave: 'p...................'},
   {name: 'es_enable'          , wave: '01..................'},
   {name: 'entropy_src_rdy_i'  , wave: '0..1...0.10.101.....'},
   {name: 'entropy_src_vld_o'  , wave: '0.....1...0.10.1.0..'},
   {name: 'entropy_src_bits_o'  , wave: 'x.....3xx4xx5xx34x..', data: ['es0','es1','es2','es3','es4','es5','es6','es7']},
 {},
]}{{< /wavejson >}}


### RNG Hardware Interface
The following waveform shows an example of what the RNG timing looks like.


{{< wavejson >}}
{signal: [
   {name: 'clk'             , wave: 'p.|......|......|......'},
   {name: 'rng_en'          , wave: '01|......|......|......'},
   {name: 'rng_ok'          , wave: '0.|1.....|......|......'},
   {name: 'es_bit_sample'   , wave:  '0.|..10..|..10..|..10....'},
   {name: 'rng_b'           , wave: 'x.|3.....|4.....|5.....', data: ['es0','es1','es2','es3','es4','es5','es6','es7']},
]}{{< /wavejson >}}


# Programmers Guide

## Initialization

The following code snippet demonstrates initializing the ENTROPY_SRC block for entropy bit generation.

```cpp

void entropy_src_init(unsigned int seed, unsigned int thresh) {

  // set the seed value
  *ES_SEED_REG = seed;

  // set the threshold value
  *ES_THRESH_REG = thresh;

  // set the configuration enable bits (digial mode)
  *ES_CONF_REG = 0x1;

  // or set the configuration enable bits (rng mode)
  *ES_CONF_REG = 0x2;

  // the ENTROPY_SRC interrupts can optionally be enabled
}
```

## Entropy Processing

The following code snippet demonstrates reading entropy bits from the ENTROPY_SRC block.

```cpp

int entropy_src_entropy(unsigned int numEntropyBits) {

  // read numEntropyBits, check for ENTROPY_SRC_INTR_STATE bit 0 
  return *ES_ENTROPY_REG;

}
```


## Error conditions

Need to alert the system of a FIFO overflow condition.


## Register Table


{{< registers "hw/ip/entropy_src/data/entropy_src.hjson" >}}
