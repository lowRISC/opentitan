---
title: "ENTROPY_SRC HWIP Technical Specification"
---

# Overview

This document specifies ENTROPY_SRC hardware IP functionality.
This module conforms to the [Comportable guideline for peripheral functionality.]({{< relref "doc/rm/comportability_specification" >}})


## Features

- The initial revision only supports an entropy source in the form of an LFSR (linear feedback shift register).
This is a pseudo-random type of entropy source, as opposed to a truly random entropy source.
A noise source and its relation to an entropy source are defined by [SP 800-90B](https://csrc.nist.gov/publications/detail/sp/800-90b/final).
- A set of registers is provided for firmware to manage and obtain entropy bits.
- The set of registers is designed such that firmware should not have to change for the case where a random source of entropy is provided in a future revision.
- Interrupts are supported:
  - Entropy bits are available.
  - An internal error has occurred.
- No SP 800-90B defined health checks are done by this revision (these functions are left for the firmware to implement).
- No alerts are supported by this revision.


## Description

This IP block provides an entropy source that is part of a larger solution to generate true random numbers (a TRNG mechanism).
The general solution for TRNG relies on firmware to orchestrate the majority of the function, getting helper services from specific hardware blocks.
For purposes of reference in this document, the NIST term "noise" will be synonymous with the term "entropy".
Likewise, no conditioning function will be performed in this block.
For the generation of entropy, this block provides the entropy bits needed for the entropy source solution as required by the firmware.

At a high-level, this ENTROPY_SRC block, when enabled, will continuously collect entropy bits from the entropy source into a FIFO that can be read from the TLUL bus.
For this revision, the entropy generation can be very fast, based on programming.
Other sources could be much slower.
The support logic in the block will support entropy sources of any rate.

Once the required number of entropy bits have been collected, the firmware has two options of notification: an interrupt, or polling.
For this revision, the `ENTROPY_RDY` bit will always be set if the {{< regref "ES_THRESH" >}} register is configured to a low value, so a firmware scheme of just reading the status bit to confirm that entropy is available is a good strategy.
For slower sources, an interrupt may be a better use of CPU cycles.

## Compatibility
This IP block does not have any direct hardware compatibility requirements.
The firmware routines, as described by SP 800-90B, must be supported.
However, as long as the function provided by the register set supports all of the call parameters, any compatibility requirements will be met.

# Theory of Operations

As already described, this IP block will collect bits of entropy for firmware consumption.
This revision is a straightforward implementation using an LFSR.
In principal, any polynomial may be used so long as it is primitive in Galois Field of order 2, or GF(2).
However, preference should be given to polynomials with the fewest number of terms.

The first step is enabling and initialization.
The main difference between these steps is that enabling is a global block enable.
The initialization step can be done at anytime while the block is enabled and running.
Before setting the `ENABLE` bit, the LFSR seed input should be initialized, using the {{< regref "ES_SEED" >}} register.
The {{< regref "ES_SEED" >}} register will transfer its value according to the initialization sequence.
After the block is enabled and initialized, entropy bits will be collected up indefinitely until disabled.

It is assumed that any entropy source will drop bits.
This means that the FIFO used to collect up the entropy bits will fill, and until the firmware starts pulling out bits, continuously generated entropy source bits may be dropped from usage.
The process of filling and draining the FIFO is the same, independent of what speed the entropy generation rate is at.

Once the `ENTROPY_RDY` status bit is set, the firmware will read the {{< regref "ES_ENTROPY" >}} register as many times as needed to get the required entropy bits, typically 128 bits or 256 bits at a time.
For ease of firmware operation, the status bit does not need to be reset.
A read of the {{< regref "ES_THRESH" >}} register could be done to verify how many entries are in the FIFO at the current time.
The {{< regref "ES_THRESH" >}} register will determine when the status bit is set, or when the interrupt will assert if enabled.
For this revision, this same {{< regref "ES_THRESH" >}} register has a range of between 1 and 32 entries in the FIFO.
An RTL parameter can be set to make this range smaller and save on gate count.

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
Once the `ENABLE` bit is set, subsequent loads of the seed into the LFSR will occur only when the `INIT_ENT_SRC` bit is set, and the state of the FIFO is full.
The intent for this is that the FIFO is in a safe state, and any attempted seed updates to the LFSR will be ignored.

A configuration/control register locking function is performed by the {{< regref "ES_REGEN" >}} register.
Clearing the bit in this register will prevent future modification of the {{< regref "ES_CONF" >}} register, the {{< regref "ES_CTRL" >}} register, or the  {{< regref "ES_SEED" >}} by firmware.

The {{< regref "ES_SEED" >}} register can be updated at any time while the entropy FIFO is in operational mode.
As long as the update sequence is followed by firmware, there will be no timing hazards when accessing these registers by the firmware.

### Entropy Processing

When enabled, the ENTROPY_SRC block will generate entropy bits continuously.
The `ENTROPY_RDY` bit in the {{< regref "ES_STATUS" >}} register will signal to the firmware when entropy bits should read from the {{< regref "ES_ENTROPY" >}} register.
While the firmware is reading the FIFO, additional entropy bits could be captured by the FIFO as long as the FIFO is not full.
The firmware will do 32-bit register reads of the {{< regref "ES_ENTROPY" >}} register to retrieve the entropy bits.
Each read will automatically pop an entry off the head of the FIFO.
New entropy bits can enter the FIFO at the tail concurrently.

Since the entropy flow is continuous, these is no tracking state machine required for the design.
Instead, the {{< regref "ES_THRESH" >}} register is used to set the point of notification to the firmware.
Notification can be either by polling or by an interrupt.
For debug, the {{< regref "ES_FDEPTHST" >}} register can be read to find out the current state of the FIFO at any time.

An additional feature is the {{< regref "ES_RATE" >}} register.
The purpose of this register is to simulate slower entropy generation sources.
This will aid firmware design and debug when trying to handle all entropy source types and rates.

### Interrupts

The ENTROPY_SRC module has two interrupts: `es_entropy_valid` and `es_entropy_fifo_err`.

The `es_entropy_valid` interrupt should be used when a entropy source has been implemented that is relatively slow.
For this revision, the entropy source can be very fast (at full rate), and polling the `ENTROPY_RDY` status bit should be done.

The `es_entropy_fifo_err` interrupt will fire when the entropy FIFO has a malfunction.
The conditions that cause this to happen are either when there is a push to a full FIFO or a pull from an empty FIFO.

### Entropy FIFO Operational Sequence
The following waveform show an example of how the entropy source is collected into the entropy FIFO.
In this example, the FIFO parameter is set to a depth of 4. The {{< regref "ES_THRESH" >}} register is set to a value of 2, and will trigger an interrupt when the FIFO has met this value.
The FIFO in this example will fill quickly, then will drain as the firmware reads the {{< regref "ES_ENTROPY" >}} register. As the entropy bits are read out, new entropy bits, if available and valid,  will immediately enter the FIFO.


{{< wavejson >}}
{signal: [
   {name: 'clk'                 , wave: 'p.......|............'},
   {name: 'es_enable'           , wave: '01......|............'},
   {name: 'es_init'             , wave: '010.....|............'},
   {name: 'fifo_push_capt_entropy', wave: '0..1...0|.10.10.10.10', data: ['ph0','ph1','ph2','ph3']},
   {name: 'entropy_bits'          , wave: 'x..3453x|.4x.5x.3x.4x', data: ['es0','es1','es2','es3','es4','es5','es6','es7']},
   {name: 'fifo_full'           , wave: '0......1|.01.01.01.01'},
   {name: 'fifo_empty'          , wave: '1..0....|............'},
   {name: 'fifo_pop_read_entropy' , wave: '0.......|10.10.10.10.'},
   {name: 'threshold reg'       , wave: '4.......|............', data: ['2']},
   {name: 'interrupt/status'    , wave: '0....1..|............'},
 {},
]}{{< /wavejson >}}


# Programmers Guide

## Initialization

The following code snippet demonstrates initializing the ENTROPY_SRC block for entropy bit generation.

```cpp

void entropy_src_init(unsigned int seed) {

  // set the seed value
  *ES_SEED_REG = seed;

  // set the configuration enable bit
  *ES_CONF_REG = 0x1;

  // the ENTROPY_SRC interrupts can optionally be enabled
}
```

## Entropy Processing

The following code snippet demonstrates reading entropy bits from the ENTROPY_SRC block.

```cpp

int entropy_src_entropy(unsigned int numEntropyBits) {

  // read numEntropyBits, check for ES_STATUS bit 0 (ENTROPY_RDY)
  return *ES_ENTROPY_REG;

}
```

## Update Seed

The following code snippet demonstrates initializing the ENTROPY_SRC block for updating the seed after initialization has been done.

```cpp

void entropy_src_seed_update(unsigned int seed) {

  // set the seed value
  *ES_SEED_REG = seed;

  // set the control initialization bit
  *ES_CTRL_REG = 0x1;

  // reset the control initialization bit
  *ES_CTRL_REG = 0x0;

}
```

## Error conditions

Need to alert the system of a FIFO overflow condition.


## Register Table


{{< registers "hw/ip/entropy_src/data/entropy_src.hjson" >}}
