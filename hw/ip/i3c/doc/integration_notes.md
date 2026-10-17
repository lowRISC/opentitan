# Integration Notes

## IP Clock Frequency

In I3C terminology there are two types of I3C bus supported by this IP block.
These are the 'Mixed Fast Bus' which incorporates both I<sup>2</sup>C targets and I3C Basic devices, and the 'Pure Bus' which supports only I3C devices.

The duration of the interval when Serial CLock (SCL) is driven high by the Active Controller is critical to the operation of an I3C 'Mixed Fast Bus'.
If the pulse is too long then the I3C traffic will not be suppressed by the spike filter of an I<sup>2</sup>C device on a 'Mixed Fast Bus' and it may cause malfunction of the I<sup>2</sup>C device.
If it is too short then it may cause communication issues with I3C Targets.

The IP block offers a top-level design parameter `ClkFreq` which specifies the frequency in Hz of the main IP clock.
Additionally there are timing parameter registers presented to software which may then specify the duration of critical time intervals in units of the IP clock period.

| Pure Bus                 | Minimum | Maximum |
|--------------------------|---------|---------|
| High period of SCL Clock | 32ns    |   N/A   |

For a 'Pure Bus' there is no maximum duration for the SCL high interval, so any reasonable IP clock frequency may be accommodated simply by increasing the number of cycles for which SCL is driven high.
A frequency range of *50MHz* (inclusive) to *1.5GHz* (inclusive) is supported by the IP block in this case, with frequencies down to _32MHz_ (exclusive) also being supported at the cost of a _proportionate decrease in the maximum signaling speed_.

| Mixed Fast Bus           | Minimum | Maximum |
|--------------------------|---------|---------|
| High period of SCL Clock | 32ns    | 41ns    |

Example clock frequencies and required tolerance:

| Clock frequency | Tolerance  | SDR      | HDR-DDR  |
|-----------------|------------|----------|----------|
| 50MHz           |  +/-2%     | 11.1Mbps | 20Mbps   |
| 55MHz           |  +/-10%    | 9.7Mbps  | 17.6Mbps |
| 85MHz           |  +/-9%     | 10.8Mbps | 19.4Mbps |

As the above table shows there is a trade off between the frequency accuracy and the achievable data rates.
Note that the quoted data rates are the effective rate of data transfer, assuming that read/write transfers are sufficiently large to mitigate the protocol overheads.
The theoretical peak signaling speeds are 12.5Mbps for SDR and 25Mbps for HDR-DDR.

It should also be observed that for frequencies between 50MHz and 100MHz there may be a requirement to reduce further the rate of data transfers to/from targets that have a large `tSCO` delay (time from SCL edge to SDA output).
This is because the Controller logic samples SDA an integral number of IP clock cycles after the SCL edge, and increasing the clock frequency extends the SCL low period to an odd number of clock cycles, moving the sampling points closer to the transitions on SCL.

## Half-cycle SCL high extension

The IP block may be parameterized to support an extension of the SCL high pulse by half of the IP clock period.
This increases the set of clock frequencies that may be used in deployments of the IP.
The half-cycle extension is achieved by forming the SCL output signal of the Controller from contributions from two flip-flops, clocked on opposing edges of the IP clock.

| Clock frequency | Tolerance  | SDR      | HDR-DDR  |
|-----------------|------------|----------|----------|
| 96MHz           |  +/-11%    | 10.6Mbps | 19.2Mbps |

The unavoidable combinational logic on the SCL output is kept as minimal as possible in the logical design and it is important at the physical level to ensure that this signal is free of glitches since SCL controls the I3C bus in its entirety.

## Impact of SCL Clock Rise and Fall Times

It is important to note that the Active Controller always drives the SCL Clock signal in push-pull mode.
In places the I3C Basic specification includes prose and diagrams that refer to 'Open Drain Timing', and it even employs the phrase 'Open Drain SCL Low Period.'
These intervals require Open Drain driving of the SDA data lane(s), and the use of modified timing, but the SCL signal is still being driven in push-pull mode by the Active Controller.

With that cautionary note stated, it should be understood that the use of 'Open Drain Timing' on a 'Mixed Fast Bus' imposes a number of constraints on the SCL Clock rise time (tCR), high period (tHIGH) and fall time (tCF) in order to ensure compatibility with I<sup>2</sup>C devices.
All of these constraints must be met simultaneously:

 - SCL Clock Rise time (tCR) must be no more than 8ns for maximum signaling frequency (fSCL = 12.5MHz).
 - SCL Clock Fall time (tCF) must be <= 8ns also, again for 12.5MHz signaling.
 - SCL Clock High period (tHIGH) when employing 'Open Drain Timing' on a 'Mixed Fast Bus' must be <= 41ns.
 - SCL Clock High period when employing 'Push-Pull Timing' on a 'Mixed Fast Bus' (tDIG_H_MIXED) must be <= 45ns.
   - This 'digital high' period is defined as tHIGH + tCF (see Figure 75 of I3C Basic Version 1.2).

In order to satisfy all of these constraints, the duration of the SCL Clock High period may need to be shortened in order to ensure that I3C traffic remains invisible to I<sup>2</sup>C Targets.
e.g. if only the worst case tCR and tCF can be met, tHIGH will need to be reduced accordingly to no more than 37ns (45ns - 8ns).

The full details may be found in Tables 49 and 50 of the Specification for I3C Basic, Version 1.2.

## I/O signals and driver styles

The IP block presents the I3C bus as two Chip I/O (CIO) pins, `scl` and `sda`, which the Controller and the Target share (see [Hardware Interfaces](interfaces.md)):

 - `cio_scl_i`, `cio_scl_o` and `cio_scl_en_o` - Serial CLock (SCL).
   Only the Controller drives SCL, and `cio_scl_en_o` is asserted while it is the Active Controller.
 - `cio_sda_i`, `cio_sda_o` and `cio_sda_en_o` - Serial DAta (SDA).
   The IP block combines the SDA drivers of the Controller and the Target onto these signals; at most one of them drives SDA at any time.

Internally, the Controller and the Target present their driver outputs using SystemVerilog compound types from the package `i3c_io_pkg`, allowing the set of signals to be modified with reduced impact upon the RTL design.
Two implementations of this package are available, and only _one_ of them shall be included in the build.
FuseSoC selects Output Driver Style 2 by default, and Output Driver Style 1 when the flag `i3c_io_sep_drv_en` is set.

### Output Driver Style 1 (`rtl/io_sep/i3c_io_pkg.sv`)

 - `sda_pp_en` - Push-pull enable for `sda`.
 - `sda_od_en` - Open drain enable for `sda`.
 - `sda` - Serial DAta line(s), gated by `sda_pp_en` and `sda_od_en`.

This style suits pads with separate push-pull and open drain drivers.
The IP top level does not yet map these signals onto the CIO pins ([#31762](https://github.com/lowRISC/opentitan/issues/31762)), so this style cannot be used at present.

### Output Driver Style 2 (`rtl/io_vod/i3c_io_pkg.sv`)

 - `sda_en` - Enable(s) for `sda`. Asserted for push-pull low/high output and for open drain low output; deasserted for open drain high output.
 - `sda` - Serial DAta line(s), gated by `sda_en`.

In this style the IP block emulates open drain signaling ('virtual open drain'), so the pads shall be configured for push-pull operation, with open drain and virtual open drain disabled.

In both styles the Controller additionally presents:
 - `scl_en` - Enable for the Serial CLock (SCL) output signal; its state depends upon whether the IP block is the Active Controller.
 - `scl` - SCL output signal, gated by `scl_en`.

## Pullups and high-keepers

In addition to the SCL and SDA signals and their respective enables, each of SCL and SDA must also support both a 'high-keeper' and a pullup resistance.
The latter is required to ensure a defined state when open drain signaling is employed, e.g. during an arbitrable address header, and the high-keepers ensure that the signal states are maintained during the transitions between push-pull signaling and open drain mode.

The Active Controller is responsible for enabling and disabling the pullups at the appropriate times during transfers, whilst the high-keepers are typically enabled throughout the time that the Controller logic is the Active Controller on the bus.
The high-keepers can however be disabled in the event that they prove inadequate for a particular bus, e.g. for reasons of track lengths or target count.
In this case, the circuit designers may provide alternative high-keepers that meet the electrical requirements of the bus.

The signals provided by the IP block are described below:

| Signal                 | Description                                                                 |
|------------------------|-----------------------------------------------------------------------------|
| `cio_ctrl_sda_pu_o`    | SDA pullup pin output; tied high                                            |
| `cio_ctrl_sda_pu_en_o` | SDA pullup pin output enable; asserted while the SDA pullup is required     |
| `ctrl_scl_pu_en_o`     | Enable for the SCL pullup; currently always deasserted                      |
| `scl_hk_en_o`          | Enable for the SCL high-keeper (`PHY_CONFIG.SCL_HK_EN`)                     |
| `sda_hk_en_o`          | Enable for the SDA high-keeper(s) (`PHY_CONFIG.SDA_HK_EN`)                  |

The SDA pullup is presented as the CIO pin `ctrl_sda_pu`, so that it can drive an external pullup resistor that is connected between this pin and SDA ('external Pull-Up resistor driven by a pin', I3C Basic Specification v1.2, Table 46).
The pin drives high while the pullup is required, and is high-impedance otherwise, so that the resistor does not load SDA during push-pull signaling.
SCL is always driven in push-pull mode by the Active Controller and needs no Open Drain pullup (I3C Basic Specification v1.2, Table 46).
The high-keeper enables are inter-module signals; an integration may leave them unconnected and use passive high-keepers on the board instead.

The internal Controller and Target drivers and signals for 'Output Driver Style 1' are illustrated in the following diagram:

![Output Style 1](drivers.svg)

## Target Reset Detector

The Target Reset Detector, `i3c_reset_detector`, detects the Target Reset Pattern on the I3C bus.
It is not part of the IP top level `i3c`; the integration instantiates it separately, typically in an Always-On power domain so that it can wake the system from 'Deepest Sleep' (see [Sleep states, power and wakeup](theory_of_operation.md#sleep-states-power-and-wakeup)).
The integration connects it as follows:

 - `clk_aon_i` and `rst_aon_ni` - the same clock and reset as the `clk_aon_i` and `rst_aon_ni` inputs of the IP block, which clock the reset detector registers.
 - `enable_i`, `req_i` and `rsp_o` - the `rstdet_enable` and `rstdet` inter-module signals of the IP block.
   If the IP block may be powered down while the detector is active, these signals must retain their values.
 - `scl_i` and `sda_i` - the SCL and SDA inputs from the pads, i.e. the same signals as `cio_scl_i` and `cio_sda_i` of the IP block.
 - `wake_up_o` - a wake-up request to the power manager; may be left unconnected if the Target need not wake the system.
 - `target_reset_o` - a reset of the I3C IP block only ('I3C Peripheral' reset).
 - `chip_reset_o` - a reset of the whole chip ('Whole Target' reset).
   The I3C Basic Specification does not require a Whole Target reset to reset the whole chip, so an integration may instead leave this output unconnected or let it reset only the I3C IP block.
   A Root of Trust should not allow an external I3C Controller to reset the whole chip.
 - `scan_clk_i` and `scanmode_i` - DFT signals.
