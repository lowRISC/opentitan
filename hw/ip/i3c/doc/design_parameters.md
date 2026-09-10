# Design Parameters

The top level of this IP block offers a number of parameters that may be used to configure the design appropriately for its intended usage.
These parameters are described below:

## Clock Frequency ('ClkFreq')

This critical design parameter specifies the frequency of the main clock into the IP block, in Hertz (cycles per second).
The logic within the IP block uses this frequency to calculate default timing parameters (in terms of clock cycles) in order to comply with the strict timing requirements of the I3C Basic Specification without relying upon software to supply correct values.
It is also important within the IP block for implementing appropriate time delays during I3C bus activity, and measuring intervals such as the 'Bus Idle' and 'Bus Available' conditions.

The supported range of clock frequencies for maximum data rate ('SDR0' at 12.5MHz) is 50MHz-1.5GHz, both inclusive, but the timing parameters support operation down to 32MHz (exclusive) if a proportionate decrease in the maximum data rate is acceptable.

## I3C Role Configuration ('PrimaryCtrl', 'SecondaryCtrl' and 'Target')

Five role configurations are intended to be supported:

| Required I3C role(s)                                                                          | PrimaryCtrl | SecondaryCtrl | Target | Available |
|-----------------------------------------------------------------------------------------------|-------------|---------------|--------|-----------|
| Primary and Secondary Controller functionality; implies Target functionality and a single bus |      1      |       1       |    1   |     -     |
| Primary Controller and Target; these may be on a single bus or separated buses                |      1      |       0       |    1   |    Yes    |
| Primary controller only                                                                       |      1      |       0       |    0   |    Yes    |
| Secondary Controller; implies Target functionality and a single bus                           |      0      |       1       |    1   |     -     |
| Target only, no Controller logic                                                              |      0      |       0       |    1   |    Yes    |

It should be noted that in this first release, operation as a Secondary Controller is not supported, so not all of these configurations are yet available.
Also, at the time of writing, the design has not been optimized to produce maximal area savings when Controller or Target functionality is excluded.

## Virtual Targets ('NumTargets' and 'MaxTargets')

Two design parameters, `NumTargets` and `MaxTargets`, are used extensively throughout the Target side of the design.
The single physical target implements a number of 'Virtual Targets', up to and including the number specified by `MaxTargets`.
If the `MaxTargets` parameter is changed then the register address space is modified, so careful consideration should be given to whether this is desirable.

To aid software portability across multiple deployments of this IP, the design parameter `NumTargets` specifies the actual number of Virtual Targets to be implemented, which should be within the range 1 to `MaxTargets`, both inclusive.
Rather than setting `NumTargets` to 0 when Target functionality is not required, the design parameters `SecondaryCtrl` and `Target` should both be set to zero, leaving the IP block performing only the Primary Controller role.

## Direct Message Buffer Access ('SWDirectMsgBuf')

The parameter `SWDirectMsgBuf` controls whether the message buffer is presented on the system bus for use as additional SRAM and/or for diagnostic use.
For an embedded system with only SRAM available, making some or all of the message buffer available in this fashion can be useful because the message buffer may constitute a significant amount of storage.

When mapped in this manner, the message buffer is bytes-addressable to the system, even though internally the I3C hardware transfers only complete 32-bit DWORDs to and from the message buffer.

## Software Execution From Message Buffer ('SWDirEnIFetch')

If direct access to the message buffer is enabled, there remains the question of whether code execution should be supported.
With the OpenTitan TL-UL interface it is possible to differentiate fetches performed by the instruction/code execution side of a CPU from regular data fetches.
This parameter determines whether instruction fetches shall be supported in addition to regular fetches as data, or whether the IP block shall instead return an error in response to an instruction fetch.

The message buffer may thus safely be configured for use as non-secure scratch data memory, for example, without permitting code execution.
Note that direct access to the message buffer does not offer the security features of the SRAM Controller that is used elsewhere within the OpenTitan project on the main SRAMs.

## Hardware Identification ('CompManufacturer', 'CompVersion' and 'CompType')

To allow a given deployment of this I3C IP block to be identified by the HCI software driver, and - where necessary - prompt the driver to adapt its behavior accordingly, the `Hardware Identification` Extended Capability is implemented.

This Extended Capability simply implements a number of Read Only registers identifying the properties of the hardware.
The presented values are taken directly from the top-level design parameters of the IP block as shown:

| Design Parameter | HCI Register Field | Description                                          |
|------------------|--------------------|------------------------------------------------------|
| CompManufacturer | COMP_MANUFACTURER  | MIPI Vendor ID, as registered with the MIPI Alliance |
| CompVersion      | COMP_VERSION       | Host Controller Component Version (Vendor-assigned)  |
| CompType         | COMP_TYPE          | Host Controller Component Type (Vendor-assigned)     |

Please see section 7.7.2 of the HCI Specification Version 1.2 for any further details.

## Half-cycle SCL Extension Support ('HalfCycleScl')

The Serial CLock (SCL) signal that is generated by the Active Controller is critical to correct operation of the I3C bus.
It is driven in push-pull mode and its timing requirements are particularly strict when supporting a 'Mixed Fast Bus' in which both full rate I3C devices and I<sup>2</sup>C devices are present.
In order to support a larger set of IP clock frequencies and/or lower clock frequency accuracy whilst still meeting the timing requirements, the IP block may be configured to support a half-cycle extension of the SCL high interval.

This half-cycle extension is achieved by also using the negative edge of the IP clock in the generation of the SCL signal, which has the disadvantage of introducing combinational logic into the SCL output path.
An important design decision within the IP is that I3C bus signals shall come directly from flip-flops wherever possible, to eliminate the possibility of glitches, and this is especially true of the SCL output.
Whilst this combinational logic is kept to a minimum, if - for a given deployment of the IP block - it is certain that the combination of clock frequency and frequency accuracy is sufficient to meet the constraints imposed upon the SCL high period, as described in HCI Tables 48, 49 and 50, then the half-cycle extension should not be enabled.

There is further information on this point in the [integration notes](integration_notes.md).

## Target Extension ('TargetExt')

In order to support protocols that are layered atop the basic I3C protocol and demand low-latency responses that may only feasibly be implemented in hardware, the Target side of the IP block offers 'Target Extension' functionality.

This interface allows a deployment of the I3C IP block to add additional logic into the design via a simplified interface at the data byte/word level, and to operate on the IP clock rather than the SCL/SDA signals of the I3C bus itself.

Any specific implementation of the 'Target Extension' interface shall declare itself via the fields `EXT_PRESENT` and `EXT_INFO` fields of the [`TARG_STATUS` register](registers.md#targ_status) and as an Extended Capability within the register address space of the IP block.
This allows the software driver to detect and adapt to the presence or absence of a specific Target Extension.
