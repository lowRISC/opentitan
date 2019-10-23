{{% lowrisc-doc-hdr Earl Grey Top Level Specification }}

{{% section1 Overview }}

<img src="earlgrey.png" align="right" alt="Earl Grey logo" title="Earl Grey" hspace="25"/>
This document specifies the top level functionality of the "Earl Grey"
chip.  This version of the chip specification is equivalent to the "0.5
netlist", not the final implementation.
It is the expected subset of functionality needed to correspond with the public launch of the OpenTitan development endeavor.
The new features and methodologies expected for 0.5 are detailed here, with discussions about the totality of its content w.r.t. our goals for the public launch.

{{% section2 Features }}

- RISC-V microprocessor ("Ibex") and associated JTAG IO. Related features:
  - DM (debug module)
  - PLIC (platform level interrupt controller)
  - U/M execution modes (user/machine)
- Memory contents
  - 512kB emulated eFlash for code and data storage
  - 64kB SRAM for data storage
  - 8kB ROM for secure boot code storage
- Security peripherals
  - Flash controller
  - AES-ECB module
  - SHA-256/HMAC module
  - Basic alert responder
  - (stretch goal) key manager
  - (stretch goal) emulated TRNG
- IO peripherals
  - 24 multiplexable IO pads
  - Two UART peripherals (using multiplexable IO)
  - GPIO peripheral (using multiplexable IO)
  - I2C host (using multiplexable IO)
  - (stretch goal) I2C device (using multiplexable IO)
  - SPI device (using fixed IO), with passthrough feature
  - SPI host (using fixed IO), with passthrough feature
- Other peripherals
  - Fixed-frequency timer
- clock and reset IO and management
- Software
  - Boot ROM implementing code signing of e-flash contents
  - Rudimentary operating system
  - Example applications and validation tests

{{% section2 Description }}

The netlist `top_earlgrey` is defined to contain just enough features to
prove basic functionality of the Ibex RISC-V processor core on an FPGA
development environment. The chosen features as defined include code
space for boot and application, UART for terminal communication, and
GPIO for basic outside-world driving and receiving.
Potential features include SPI communication for boot-time code loading, but the fallback is to use JTAG, or have the FPGA environment push code into the SRAM before reset and have the processor boot from there.

The netlist `top_earlgrey` is defined to contain enough features to prove some security functionality heading towards the final OpenTitan definition, working in an FPGA development environment.
The chosen features add on top of the basic proof-of-concept functionality of the 0.1 netlist, adding in I2C and SPI host peripheral functionality, secure boot using ROM and emulated e-flash macros, some cryptography basics in AES and SHA/HMAC, and the beginnings of some physical defense in the alert responder.
As a stretch goal - depending upon schedule and staffing realities - it adds an emulated TRNG (a digital wrapper around a behavioral model representing an analog design) and a key manager.
On the IO side, it adds multiplexable IO pins to show the flexible routing concepts there, but still retains external clock and reset control rather than fundamentally secure internally generated clock and reset structures.
Another primary improvement in 0.5 is the methodology that generates the chip itself.
Rather than a hand-crafted top-level netlist, the top is stitched together with a script that reads content files in `hjson` that describe the full design.
This script (or set of scripts) generates the interconnecting crossbar (via `TLUL`) as well as the instantiations at the top level.
It also feeds into the document generation to ensure that the chosen address locations are documented automatically using the data in the source files.

{{% section1 Theory of Operations }}

{{% section2 Block Diagram }}

![Top Level Block Diagram](top_earlgrey_block_diagram.svg)

{{% section2 Hardware Interfaces }}

| Signal Name | Direction | Description |
| --- | --- | --- |
| `IO_CLK`    | input  | Chip level functional clock |
| `IO_RST_N`  | input  | Chip level reset, active low |
| `IO_JTCK`   | input  | JTAG Clock |
| `IO_JTMS`   | input  | JTAG Test Mode Select |
| `IO_JTDI`   | input  | JTAG Test Data In |
| `IO_JTDO`   | output | JTAG Test Data Out |
| `IO_JRST_N` | output | JTAG Test Reset |
| `IO_SDCK`   | input  | SPI device clock |
| `IO_SDCS`   | input  | SPI device chip select |
| `IO_SDDI`   | input  | SPI device input data |
| `IO_SDDO`   | output | SPI device output data |
| `IO_SHCK`   | output | SPI host clock |
| `IO_SHCS`   | output | SPI host chip select |
| `IO_SHDI`   | output | SPI host input data |
| `IO_SHDO`   | input  | SPI host output data |
| `MIO_00` .. `MIO_23` | inout  | Multiplexible pins available for input or output connections with peripheral units' (UART, GPIO, etc.) IO |

{{% section2 Design Details }}

This 0.5 version of the top level design contains features to prove some fundamental security functionality through some basic peripherals.
This section provides some details for the processor and the peripherals.
See their representative specifications for more information.
This section also contains an overview of the holistic security features in this version, with a hint to the direction of the security features of the final product.

### Clocking and Reset

For this version of the chip, clock and reset come from outside the
device.  Eventually these will be generated internally to reduce risk
of security attack, but the complexity for internal clock generation
is not warranted for initial implementation. The clock pin is `IO_CLK`
and all of the design is synchronous to this one clock. (Exceptions are
peripheral IO that might be synchronized to a local peripheral clock
like JTAG TCK or SPI device clock).

Deassertion of the active low reset pin `IO_RST_N` causes the processor to
come out of reset and begin executing code at its reset vector.
The reset vector begins in ROM, whose job is to validate code in the emulated e-flash before jumping to it.
The assumption is that the code has been instantiated into the e-flash before reset is released.
This can be done with JTAG commands (see that section),
or through virtual assignment in verification.
The SPI device can be used to load e-flash instruction content.
Resets throughout the design are asynchronous active low.
Other resets may be generated internally via the alert responder, watchdog timer, etc., and other resets for subunits may be disseminated.
These will be detailed in this section over time.

### Main processor (`core_ibex`)

The main processor (`core_ibex`) is a RISC-V core based upon the PULPino
zero-riscy core, modified to meet Comportability requirements. See the
[core_ibex specification](https://ibex-core.readthedocs.io/en/latest/)
for more details of the core.
In addition to the standard RISC-V functionality, Ibex implements M (machine) and U (user) mode per the RISC-V standard.
Attached to the Ibex core are a debug module (DM) and interrupt module (PLIC).

#### JTAG / Debug module

One feature available for Earl Grey processor core is debug access.
By interfacing with JTAG pins, logic in the debug module allows the core to enter debug mode (per RISC-V 0.13 debug spec), and gives the design the ability to inject code either into the device - by emulating an instruction - or into memory.

The commands and addresses to implement these features are TBD at this
time, and will be further detailed in later specification releases.

[DM Specification](https://github.com/pulp-platform/riscv-dbg/)

#### Interrupt Controller

Adjacent to the Ibex core is an interrupt controller that implements the RISC-V PLIC standard.
This accepts a vector of interrupt sources within the device, and assigns leveling and priority to them before sending to the core for handling.
See the details in the Ibex specification.


See also the
[OpenTitan PLIC specification](https://bubble.servers.lowrisc.org/hw/ip/rv_plic/doc/rv_plic.html)
for more details.

#### Performance

Ibex currently achieves a [CoreMark](https://www.eembc.org/coremark/) per MHz of 2.36 on the earlgrey verilator system.
Performance improvements are ongoing, including the following items being considered:

1. Adding a new ALU to calculate branch targets to remove a cycle of latency on taken conditional branches (currently the single ALU is used to compute the branch condition then the branch target the cycle following if the branch is taken).
2. A 3rd pipeline stage to perform register writeback, this will remove a cycle of latency from all loads and stores and prevent a pipeline stall where a response to a load or store is available the cycle after the request.
3. Implement a single-cycle multiplier.
4. Produce an imprecise exception on an error response to a store allowing Ibex to continue executing past a store without waiting for the response.

The method for including these features, e.g. whether they will be configurable options or not, is still being discussed.

The Ibex documentation has more details on the current pipeline operation, including stall behaviour for each instruction in the [Pipeline Details](https://ibex-core.readthedocs.io/en/latest/pipeline_details.html) section.

The CoreMark performance achieved relies in part on single-cycle access to instruction memory.
An instruction cache is planned to help maintain this performance when using flash memory that will likely not have single-cycle access times.

CoreMark was compiled with GCC 9.2.0 with flags: `-march=rv32imc -mabi=ilp32 -mcmodel=medany -mtune=sifive-3-series -O3 -falign-functions=16 -funroll-all-loops -finline-functions -falign-jumps=4 -mstrict-align`

### Memory

The device contains three memory address spaces for instruction and data.

Instruction ROM (8kB) is the target for the Ibex processor after release of external reset.
The ROM contains hard-coded instructions whose purpose is to do a minimal subset of platform checking before checking the next stage of code.
The next stage - a boot loader stored in embedded flash memory - is the first piece of code that is not hard-coded into the silicon of the device, and thus must be signature checked.
The ROM executes this signature check by implementing a RSA-check algorithm on the full contents of the boot loader.
The details of this check will come at a later date.
For verification execute-time reasons, this RSA check will be overridable in the FPGA and verification platforms (details also TBD).
This is part of the *Secure Boot Process* that will be detailed in a security section in the future.

Earl Grey contains 512kB of emulated embedded-flash (e-flash) memory for code storage.
This is intended to house the boot loader mentioned above, as well as the operating system and application that layers on top.
For the 0.5 version the expectation is that the operating system will be very lightweight, and the "application" will be simple proof of concept code to show that the chip can do.
One example will be validation code that tests the validity and stability of the full chip environment itself.

Embedded-flash is the intended technology for a silicon design implementing the full OpenTitan device.
It has interesting and challenging parameters that are unique to the technology that the silicon is implemented in.
Earl Grey, as an FPGA-only proof of concept, will model these parameters in its emulation of the memory in order to prepare for the replacement with the silicon flash macros that will come.
This includes the read-speeds, the page-sized erase and program interfaces, the two-bank update scheme, and the non-volatile nature of the memory.
Since by definition these details can't be finalized until a silicon technology node is chosen, these can only be emulated in the FPGA environment.
We will choose parameters that are considered roughly equivalent of the state of the art embedded-flash macros on the market today.

Details on how e-flash memory is used by software will be detailed in the Secure Boot Process and Software sections that follow.

The intent is for the contents of the embedded flash code to survive FPGA reset as it would as a NVM in silicon.
How this functions in FPGA is TBD.
Loading of the FPGA with initial content, or updating with new content, is also TBD at this time.
The SPI device peripheral is intended as a method to bulk-load e-flash memory.
The processor debug port (via JTAG) is also available for code loading.
Details will follow.

Also included is a 64kB scratch pad SRAM available for data storage (stack, heap, etc.) by the Ibex processor.
It is also available for code storage, but that is not its intended purpose.

The base address of the ROM, Flash, and SRAM are given in the address map section later in this document.

### Peripherals

Earl Grey contains a suite of "peripherals", or subservient execution units connected to the Ibex processor by means of a bus interconnect.
Each of these peripherals follows an interface scheme dictated in the
[Comportability Specification.](../../../doc/rm/comportability_specification.md)
This specification details how the processor communicates with the peripheral (via TLUL interconnect); how the peripheral communicates with the chip IO (via fixed or multiplexable IO); how the peripheral communicates with the processor (interrupts); and how the peripheral communicates security events (via alerts).
See that specification for generic details on this scheme.

The peripherals included within Earl Grey for 0.5 functionality were chosen to give some basic outside-world communication, the beginnings of a security roadmap for the device, internal housekeeping, and processor control.
These are described briefly for each peripheral below.
Where available today, detailed specifications will be linked.
In other cases, the details will come as the peripherals are fully specified.
Some of the peripherals are aspirational for this release, and are a function of the staffing realities between the time of this writing and 0.5 release.
Those are noted in the descriptions below.
The address for each of the peripherals will be given at the end of this document in an auto-generate address map based upon the source configuration files for Earl Grey.

#### Chip IO Peripherals

##### Pin Multiplexor (`pinmux`)

The pin multiplexor serves two purposes: routing between peripherals and the available multiplexable IO (`MIO_00 .. MIO_23`); and pin control (drive strength and technology (OD, OS, etc)) for the MIO and fixed-function IO.
For the 0.5 release, this routing and pin control is a subset of the final features required in OpenTitan, but gives an example of the flexibility allowed by this multiplexing scheme.

The pinmux is itself a peripheral on the TLUL bus, with its collection of registers that define the connectivity between other peripherals with IO and the chip pads.
These registers include a selection of every chip output as to which peripheral output drives it; a selection of every peripheral input as to what chip input drives it; and pad control for all pin IO.
Details for this module will come at a later date.
See the
[pinmux specification](https://bubble.servers.lowrisc.org/hw/ip/pinmux/doc/pinmux.html)
for how to connect peripheral IO to chip IO.

##### UART

The chip contains two UART peripherals that implement single-lane duplex UART functionality.
There are two versions of the same UART included in the 0.5 release.
Their outputs and inputs can be configured to any chip IO via the pinmux.
See the
[UART specification](https://bubble.servers.lowrisc.org/hw/ip/uart/doc/uart.html)
for more details on this peripheral.

##### GPIO

The chip contains one GPIO peripheral that creates 32 bits of bidrectional communication with the outside world via the pinmux.
Since currently only 24 pins of multiplexable IO (MIO) are specified for Earl Grey, not all of its capability can be realized at this time.
But via pinmux any of the 32 pins of GPIO can be connected to any of the 24 chip pins, in any direction.
See the
[GPIO specification](https://bubble.servers.lowrisc.org/hw/ip/gpio/doc/gpio.html)
for more details on this peripheral.
See the
[pinmux specification](https://bubble.servers.lowrisc.org/hw/ip/pinmux/doc/pinmux.html)
for how to connect peripheral IO to chip IO.

##### SPI device

In addition to the SPI passthrough functionality (see below), the SPI device for the 0.5 release will implement Firmware Mode as was included in the 0.1 release.
This feature provides the ability for external drivers to send firmware upgrade code into a bank of embedded flash memory for in-field firmware updates.
Firmware mode has no addressing, and at the moment no other addressing modes are anticipated for the 0.5 release though this might change as the detailed specification for the proof of concept for SPI passthrough is crafted.
For the 0.5 release only single-mode functionality is required.

See the
[SPI device specification](https://bubble.servers.lowrisc.org/hw/ip/spi_device/doc/spi_device.html)
for more details on the Firmware Mode implementation.

For SPI passthrough timing reasons, the SPI device pins will be hardwired to Earl Grey chip IO pins as shown in the block diagram above.

##### SPI host

In addition to the SPI passthrough functionality (see below), the SPI host is able to originate SPI transactions as directed by software.
This functionality will require addressing modes, as well as "generic transfer" where the data is simply sent as contained packets by the host hardware state machine.
The specification for SPI host is not defined at this time, and will depend upon conversations with the software team which are still in development.
Only single-mode functionality is expected at this time.

For SPI passthrough timing reasons, the SPI host pins will be hardwired to Earl Grey chip IO pins as shown in the block diagram above.

##### SPI passthrough (utilizing SPI device and host)

One primary feature of the 0.5 release is to develop at least rudimentary SPI Passthrough functionality.
This feature allows Earl Grey to interpose on SPI, watching transactions coming in to the SPI device port, and passing them on to the SPI host port.
The involvement of the SPI device and host components (working together) requires logic to inspect the activities of the SPI transfer, and potentially modify them on the way out, with minimal latency impact.
This is implemented with a simple MUX between the device and host pins to select either the inbound device traffic, or pre-created "safe" content.
The MUX is simple, but the selection of it requires inspection logic and a lookup table to determine safe and unsafe behavior, as well as the replacement safe transaction.
The specification for this functionality will be created in conjunction with systems designers who are using similar behavior in products today.
The goal is for this subset of functionality provide enough proving ground to a) show the direction of the concept; b) test out software interfaces with the system to be developed around it.
It is within the realm of possibility that we do not get enough system- and software-feedback in order to specify this sufficiently to be worth including within 0.5 release (in which case SPI host can also be dropped), but it is an important enough feature in the long run for OpenTitan to attempt to tackle it early.

##### I2C host

In order to be able to command I2C devices on systems where Earl Grey will be included, I2C host functionality is required.
This will include standard, full, and fast mode, up to 1Mbaud.
The details of the I2C host module will come in a later specification.
The pins of the I2C host will be available to connect to any of the multiplexable IO (MIO) of the Earl Grey device.
More than one I2C host module might be instantiated in this release.
I2C device (aspirational)
It is a stretch goal to include an independent I2C device module, receiving I2C commands up to fast mode speed.
This is not a hard requirement for 0.5 and is considered of lowest priority at this time.
If included, a full specification will be given at that time.
The pins of the I2C device would be available to connect to any of the multiplexable IO (MIO) of the Earl Grey device.

#### Security Peripherals

The 0.5 release will include the beginnings of some security peripherals and subsystems to head towards the full silicon security architecture required for the final OpenTitan device.
A security section will follow later to show how these work together.

##### AES

[AES](https://nvlpubs.nist.gov/nistpubs/fips/nist.fips.197.pdf)
is the primary
[symmetric encryption](https://en.wikipedia.org/wiki/Symmetric-key_algorithm)
and decryption mechanism used in OpenTitan protocols.
AES runs with key sizes of 128b, 192b, or 256b.
The module can select encryption or decryption of data that arrives in 16 byte quantities to be encrypted or decrypted independently of other data
("[ECB mode](https://en.wikipedia.org/wiki/Block_cipher_mode_of_operation#ECB)").
Other modes (say
[CTR mode](https://en.wikipedia.org/wiki/Block_cipher_mode_of_operation#CTR),
[CBC mode](https://en.wikipedia.org/wiki/Block_cipher_mode_of_operation#CBC),
etc) can be implemented in software on top of the results of ECB, though future versions of this AES IP will likely add such overlayed modes in hardware to improve performance and increase security (risk of secret exposure).
For this version, all data transfer is "front door" in the sense that key and data material is passed into the module via register writes.
Future versions will have provisions for private transfer of key and data material to reduce exposure from potentially untrusted local firmware.
This version does not attempt to add any side-channel or fault-injection resistance into the design.
Future versions will begin to add in such countermeasures.

In short, this version of AES is a functional proof of concept of the algorithm that will be augmented to its final hardened state for silicon implementation purposes.

Details on how to write key and data material into the peripheral, how to initiate encryption and decryption, and how to read out results, will be given in a forthcoming AES specification.

##### SHA-256/HMAC

SHA-256 is the primary
[hashing algorithm](https://en.wikipedia.org/wiki/Cryptographic_hash_function)
used in OpenTitan protocols.
SHA-256 is a member of the
[SHA-2](https://en.wikipedia.org/wiki/SHA-2)
family of hashing algorithms, where the digest (or hash output) is of 256b length, regardless of the data size of the input to be hashed.
The data is sent into the SHA peripheral after declaring the beginning of a hash request (effectively zeroing out the internal state to initial conditions), 32b at a time.
Once all data has been sent, the user can indicate the completion of the hash request (with optional partial-word final write).
The peripheral will produce the hash result available for register read by the user.
All data transfer is "front door" in the sense that it is passed into the module via register writes.
Future versions will have provisions for private transfer of data to reduce exposure from potentially untrusted local firmware.
This version does not attempt to add any side-channel or fault-injection resistance into the design.
Future versions will begin to add in such countermeasures.

[HMAC](https://en.wikipedia.org/wiki/HMAC)
is a message authentication protocol layered on top of a hashing function (in this case SHA-256), mixing in a secret key for cryptographic purposes.
HMAC is a particular application of appending the secret key in a prescribed manner, twice, around the hashing (via SHA-256) of the message.
It is a stretch goal to add HMAC functionality on top of the SHA-256 functionality for the Earl Grey SHA-256 peripheral.
For this functionality, a 256b key must be programmed into the module before the message hash can begin.
Otherwise the interface to the peripheral is as described above.
The timing of authentication completion will vary, being longer in latency than native SHA-256.
The similar commentary about the security of data transfer on SHA-256 above applies to HMAC, especially as regards the secret key.
Details on how to write key and data material into the peripheral, how to initiate hashing / authentication, and how to read out results, will be given in a forthcoming SHA specification.

##### Key Manager (aspirational)

The creation, dissemination, and storage of key material is one of the critical functions of the final OpenTitan design.
The primary facilitator of these functions is the key manager module.
This module operates in four primary modes:
the initial personalization and creation of the identity key at manufacturing time;
the communication of the identity at manufacturing time;
the regeneration of the identity key as needed during production use;
and the wrapping of other keys based upon the identity key during production use.

**Mode 1**: Personalization

The initial personalization of the device converts a raw unpersonalized part into one that has a unique cryptographically strong identity that is permanently paired with the device.
This process can only be done once, and one done in manufacturing.
This process does not require any communication with the outside world other than the loading of the software to execute the steps.
These steps include gathering partial identity material (numerical values) stored in various parts of the device.
Some of these parts are common across all devices; others are unique per device, stored in non-volatile memory components.
The latter must be randomly generated during this personalization step, then locked down so that they are never modifiable again.
Then, the gathering process uses the key manager, which executes a repeatable sequence of steps implementing a mixing (hashing) process using the HMAC module.
A likely example is the DRBG process as outlined by
[NIST publication 800-90A](http://dx.doi.org/10.6028/NIST.SP.800-90Ar1).
The personalization step (creation of the random partial secrets) is only done once, and only at manufacturing.

**Mode 2**: Communication of Identity

After the personalization step, and after the first gathering of the identity, the part must communicate the identity to the outside world.
This is done with a secure delivery channel that is set up in the communication process.
The key manager ensures that the channel has been set up correctly before allowing the transmission of an encrypted message containing the identity.
The communication step is only done once, and only at manufacturing.

**Mode 3**: Regeneration of the Identity

The identity of the device is never stored at rest.
Any time the identity is required during production mode execution, it must be regenerated from the stored partial secret material.
This regeneration step is identical to the one executed in mode 1 during manufacturing, but the identity can now never leave the device.
The key manager executes the same mixing steps to generate the identity, which stays within the key manager.
Software can test the identity during production mode, but can not extract it from the manager.
After it is used, software should wipe the identity so that it is not stored internally on the device for any length of time.

**Mode 4**: Key wrapping

The device can create other less security-critical keys as a function of the basic identity key.
It can do this by executing hashing steps with the key manager, starting with the identity key and adding other values writeable by software.
These keys can be shared with firmware and used as needed by the application running on the device.
The wrapping uses the key manager to execute similar steps as the DRBG process, adding in software writeable constants as needed.

In all of these modes, the key manager needs to be commanded to execute particular steps using the SHA/HMAC (for hashing) and AES (for encryption) engines.
Data must be kept in private buses between the different engines and from the storage of the partial secret material.
The management of these steps and the transmission of the data is the job of the key manager, as is the protection of the resultant material based upon the state of the device and the mode of execution.

Further details of the key manager are TBD.
As of this writing, the key manager is a goal not a requirement of the 0.5 release.
If included, it will likely not include all of the required features, but a subset to allow for early testing.

##### Alert Manager

Alerts, as defined in the Comportability Specification, are defined as security-sensitive interrupts that need to be handled in a timely manner to respond to a security threat.
Unlike standard interrupts, they are not solely handled by software.
Alerts trigger a first-stage request to be handled by software in the standard mode as interrupts, but trigger a second-stage response by the alert manager if software is not able to respond.
This ensures that the underlying concern is guaranteed to be addressed if the processor is busy, wedged, or itself under attack.

Each peripheral has an option to present a list of individual alerts, representing individual threats that require handling.
These alerts are sent in a particular encoding method to the alert manager module, itself a peripheral on the system bus.
The alert manager creates one processor interrupt per alert, but also keeps track of the amount of time between reception (setting) and handling (clearing) of the interrupt.
If the time is beyond a configurable duration, then the manager raises the response, either via an NMI (higher level non-maskable interrupt), a lowering of the current execution privilege level, a request of wipe sensitive chip state, or a reset of the device.
These responses are not described in further detail at this time, but the basics of the configuration methods will be designed in this version of the alert manager.

In addition, signaling exists between the alert manager and each peripheral to ensure that all monitors are active.
This "heartbeat check" requests a response from the alert senders over the same wires to ensure that their reporting mechanism has not itself been compromised.
More details about the alert manager will come in an independent alert manager specification.

##### TRNG (aspirational)

Randomness is a critical part of any security chip.
It provides variations in execution that can keep attackers from predicting when the best time is to attack.
It provides secret material used for identity and cryptographic purposes.
It can be seeded into algorithmic computation to obscure sensitive data values.
In short, it is a source of critical functionality that must be designed to be truly random, but also free from attack itself.

Most
[TRNG](https://en.wikipedia.org/wiki/Hardware_random_number_generator)s
(True Random Number Generators) are analog designs, taking advantage of some physical event or process that is non-deterministic.
Example designs rely on metastability, electronic noise, timing variations, thermal noise, quantum variation, etc.
These are then filtered and sent into a pool of entropy that the device can sample at any time, for whatever purposes are needed.
The creation, filtering, storage, protection, and dissemination of the randomness are all deep topics of intense research in their own right.
Since the design is likely to be an analog design tied to the final chosen silicon technology process, our FPGA implementation can only approximate the results.
We can however fully specify the software interface to the TRNG in a digital wrapper.

The primary interface to the entropy pool is a read request of available random bits.
The TRNG interface can indicate how many bits are available, and then software can read from this pool, if available.
Reading of entropy that is not available should immediately trigger an interrupt or an alert.
In FPGA we can emulate the randomness with something akin to a
[PRBS](https://en.wikipedia.org/wiki/Pseudorandom_binary_sequence).

At this time the TRNG is aspirational in the sense that it is not a committed design for the 0.5 release, but will be implemented if staffing allows.
At that time a detailed specification for the pseudo-TRNG implemented in FPGA would be given.

#### Other peripherals

##### Timer(s)

Timers are critical for operating systems to ensure guaranteed performance for users.
To some level they are even required by the RISC-V specification.
At this time, two primary timers are envisioned for this version of the netlist.
First is a 64b free running timer with a guaranteed (within a certain percentage) frequency.
Second is a watchdog timer that can be used to backstop the processor in the case of it being unresponsive (usually due to development code that is wedged, rather than for instance due to security attack).
The goal is for both of these to be satisfied in a unified timer module, which may have different timers for different purposes.
In future, requirements for low power functionality (when the primary high precision high speed system clock is inactive) will likely be added.

The specification for the timer can be found
[here](https://bubble.servers.lowrisc.org/hw/ip/timer/doc/timer.html).

##### Flash Controller

The final peripheral discussed in this release of the netlist is an emulated flash controller.
As mentioned in the memory section, up to 512kB of emulated embedded flash will be available for code and data storage.
The primary read path for this data is in the standard memory address space.
Writes to that address space are ignored, however, since one can not write to flash in a standard way.
Instead, to write to flash, software must interaction with the flash controller.

Flash functionality include three primary commands: read, erase, and program.
Read as mentioned above is standard, and will use the memory address space.
Erase is done at a page level, where a page is dependent upon the flash macro block that will eventually be defined by the silicon provider.
For our purposes, we define a page as 1kB in size.
Upon receiving an erase request, the flash controller will wipe all contents of that 1kB page, rendering the data in all `1`s state (`0xFFFFFFFF` per word).
Afterwards, software can program individual words to any value.
It is notable that software can continue to attempt to program words even before another erase, but it is not physically possible to return a flash bit back to a `'1'` state without another erase.
So future content is in effect an AND of the current content and the written value.

  `next_value = AND(current_value, write_word)`

Erase and program are slow.
A typical erase time is measured in milliseconds, program times in microseconds.
Bulk (multi-word) program options will be provided to alleviate this impact, but this clearly changes the behavioral model of software, and thus emulating this in FPGA is critical to begin developing code with these times in mind.
The flash controller peripheral in this release will approximate those expected times.

Security is also a concern, since secret data can be stored in the flash.
At this time the data protection around the flash macro is not discussed, but future protection in the form of ECC or CRC checks will be detailed.
A fully specified flash controller module will be specified in the future.

### Interconnection

Interconnecting the processor and peripheral and memory units is a bus
network built upon the TileLink-Uncached-Light protocol. See the
[OpenTitan bus specification](https://bubble.servers.lowrisc.org/hw/ip/tlul/doc/tlul.html)
for more details.

{{% section2 Register Table }}

The base and bound addresses of the memory and peripherals are given in this
table below. This is cut/paste at the moment, will be automated in the future.

The choice of memory, or lack thereof at location 0x0 confers two exclusive benefits
* If there are no memories at location 0x0, then null pointers will immediately error and be noticed by software (the xbar will fail to decode and route)
* If SRAM is placed at 0, accesses to data located within 2KB of 0x0 can be accomplished with a single instruction and thus reduce code size.

For the purpose of top_earlgrey, the first option has been chosen to benefit software development and testing

| Item | base address | bound address |
| --- | --- | --- |
| ROM           | `0x00008000` | `0x00001fff` |
| SRAM          | `0x10000000` | `0x1000ffff` |
| debug\_ram    | `0x1a110000` | `0x1a11ffff` |
| Flash (read)  | `0x20000000` | `0x2007ffff` |
| UART0         | `0x40000000` | `0x4000ffff` |
| UART1         | `0x40010000` | `0x4001ffff` |
| GPIO          | `0x40020000` | `0x4002ffff` |
| SPI device    | `0x40030000` | `0x4003ffff` |
| SPI host      | `0x40040000` | `0x4004ffff` |
| I2C device    | `0x40050000` | `0x4005ffff` |
| I2C host      | `0x40060000` | `0x4006ffff` |
| pinmux        | `0x40070000` | `0x4007ffff` |
| timer         | `0x40080000` | `0x4008ffff` |
| rv\_plic      | `0x40090000` | `0x4009ffff` |
| flash\_ctrl   | `0x40100000` | `0x4010ffff` |
| aes           | `0x40110000` | `0x4011ffff` |
| hmac          | `0x40120000` | `0x4012ffff` |
| keymgr        | `0x40130000` | `0x4013ffff` |
| trng          | `0x40140000` | `0x4014ffff` |
| alert\_handler| `0x40150000` | `0x4015ffff` |
