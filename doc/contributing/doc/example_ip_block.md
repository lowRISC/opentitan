# An Example IP Block's Documentation

## The summary/index file

Typically the documentation of an IP block follows the same broad outline.
`README.md` at the root of the blocks directory holds a summary of the block.
This starts with the name of the IP block as a title followed by an overview section with some boiler-plate comments.

````md
# Example IP Block
## Overview

This document specifies Name hardware IP functionality.
This module conforms to the [Comportable guideline for peripheral functionality.](/doc/contributing/hw/comportability/README.md)
See that document for integration overview within the broader top level system.
````

The next section summarizes the feature set of the IP block.

````md
### Features

- Bulleted list
- Of main features
````

There then follows a general description of the IP.

````md
### Description

Description of the IP.
````

The Compatibility information will allow device driver writers to identify existing code that can be used directly or with minor changes.
*This section is primarily of interest to software engineers.*

````md
### Compatability

Notes on if the IP register interface is compatible with any existing register interface.
Also note any differences.
For example: Matches 16550 UART interface but registers are at 32-bit word offsets.
````

The reader is then given links to more detailed documentation.
Notice, the Design Verification page is the index of the subdirectory, `./dv/README.md`, it describes.

````md
## Further Reading

- [Theory of Operation](./doc/theory_of_operation.md)
- [Programmer's Guide](./doc/programmers_guide.md)
- [Design Verification](./dv/README.md)
- [Hardware Interfaces](./doc/interfaces.md)
- [Register](./doc/registers.md)
````

## The Theory of Operations file

In the `doc/theory_of_operation.md` file lives a more detailed operational description of the module.
Conventionally one of the first sections includes a block diagram and a description.
*This should be useful to hardware designers, verification engineers and software engineers.*
There is then a design details section the organization of which is done to suit the module.

````md
# Theory of Operations
## Block Diagram

![Name Block Diagram](block_diagram.svg)

## Design Details

Details of the design.

### Many third level headings

There are probably waveforms embedded here:
````


## The Programmer's Guide file

In the `doc/programmers_guide.md` file is the software user guide and describes using the IP and notes on writing device drivers.
Code fragments are encouraged.
*This section is primarily for software engineers, but it is expected that the code fragments are used by verification engineers.*

````md
# Programmers Guide
````

One important thing here is to show the order of initialization that has been tested in the verification environment.
In most cases other orders will work, and may be needed by the software environment, but it can be helpful in tracking down bugs for the validated sequence to be described!

````md
## Initialization

```c

 if (...) {
   a = ...
 }
```
````

Other sections cover different use cases and example code fragments.

````md

## Use case A (e.g. Transmission)

## Use case B (e.g. Reception)

````

It is important to include a discussion of error conditions.

````md
## Error conditions

````

Also comment on anything special about interrupts, potentially including the priority order for servicing interrupts.

````md
## Interrupt Handling

````

## Hardware Interfaces and Registers files

The `doc/interfaces.md` and `doc/registers.md` contain primarily generated content.
The hardware interfaces and register tables respectively.

Hardware interfaces containing a description of the IP including the signals, interrupts and alerts that the block uses.
*Primary user is the SoC integrator, but useful for everyone.*
Note that the interrupt descriptions are also automatically placed in the interrupt status register bit descriptions, which is the most likely place for software engineers to reference them.

The generated content is inserted using [`CMDGEN`](./README.md#cmdgen).

````md
# Hardware Interfaces

Additional information before

<!-- BEGIN CMDGEN #util/regtool.py --interfaces ./hw/ip/example/data/example.hjson -->

<!-- END CMDGEN -->

and after the generated content.
````

````md
# Registers

<!-- BEGIN CMDGEN #util/regtool.py -d ./hw/ip/example/data/example.hjson -->

<!-- END CMDGEN -->
````

*Note, one should remove the `#` before the commands.
This is there so that `CMDGEN` doesn't try to generate registers for the non existent 'example' block.*
