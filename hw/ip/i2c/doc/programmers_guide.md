# Programmer's Guide

## Initialization

After reset, the initialization of the I2C HWIP primarily consists of four steps:
1. Timing parameter initialization
1. FIFO reset and configuration
1. Interrupt configuration
1. Enable I2C Host or Target functionality

### Timing Parameter Tuning Algorithm

Of the four initialization steps, the timing parameter initialization is the most involved.  With so many timing parameters, it is essential to have dedicated device interface functions (DIFs) to determine appropriate values for the 10 timing parameters.

The values of these parameters will depend primarily on three bus details:
- The speed mode of the slowest device on the bus: Standard-mode (100 kbaud), Fast-mode (400 kbaud) or Fast-mode Plus (1 Mbaud).
- The input clock period, t<sub>clk</sub> in ns.
- The expected signal rise time, t<sub>r</sub>, in ns.
    - This is not a firmware-controlled parameter.
    Rather, it is a function of the capacitance and physical design of the bus.
    The specification provides detailed guidelines on how to manage capacitance in an I2C system:
    - Section 5.2 of the I2C specification indicates that Fast-mode Plus devices may operate at reduced clock speeds if the bus capacitance drives signal rise times (t<sub>r</sub>) outside the nominal 120ns limit.
    Excess capacitance can also be compensated for by reducing the size of the bus pullup resistor, so long as the total open-drain current does not exceed 20mA for Fast-mode Plus devices (as described in section 7.1 of the I2C specification).
    However the specification places a hard limit on rise times capping them at 1000ns.
    - If there are Standard- or Fast-mode target devices on the bus, the specified open-drain current limit is reduced to 3mA (section 7.1), thus further restricting the minimum value of the pull-up resistor.
    - In Fast-mode bus designs, where the total line capacitance exceeds 200pF, the specification recommends replacing the pull-up resistor with an active current source, supplying 3mA or less (section 5.1).
    Regardless of the physical construction of the bus, the rise time (t<sub>r</sub>) is a system dependent, parameter that needs to be made known to firmware for I2C initialization.
- The expected fall time, t<sub>f</sub>, in ns.
    - Like t<sub>r</sub>, this parameter is not firmware controlled rather it is a function of the SCL driver, which in a strictly compliant device is expected to manage the slew-rate for the falling edge of the SDA and SCL signals, through proper design of the SCL output buffer.
    - See table 10 of the I2C specification for more details.
- (optional) The desired SCL cycle period, t<sub>SCL,user</sub> in ns.
    - By default the device should operate at the maximum frequency for that mode.
    However, If the system developer wishes to operate at slower than the mode-specific maximum, a larger than minimum period  could be allowed as an additional functional parameter when calculating the timing parameters.

Based on the inputs, the timing parameters may be chosen using the following algorithm:
1. The physical timing parameters t<sub>HD,STA</sub>, t<sub>SU,STA</sub>, t<sub>HD.DAT</sub>, t<sub>SU,DAT</sub>, t<sub>BUF</sub>, and t<sub>STO</sub>, t<sub>HIGH</sub>, and t<sub>LOW</sub> all have minimum allowed values which depend on the choice of speed mode (Standard-mode, Fast-mode or Fast-mode Plus).
Using the speed mode input, look up the appropriate minimum value (in ns) for each parameter (i.e. t<sub>HD,STA,min</sub>, t<sub>SU,STA,min</sub>, etc)
1. For each of these eight parameters, obtain an integer minimum by dividing the physical minimum parameter by the clock frequency and rounding up to the next highest integer:
$$ \textrm{THIGH_MIN}=\lceil{t\_{HIGH,min}/t\_{clk}}\rceil $$
$$ \textrm{TLOW_MIN}=\lceil{t\_{LOW,min}/t\_{clk}}\rceil $$
$$ \textrm{THD_STA_MIN}= \lceil{t\_{HD,STA,min}/t\_{clk}}\rceil $$
$$ \textrm{TSU_STA_MIN}= \lceil{t\_{SU,STA,min}/t\_{clk}}\rceil $$
$$ \textrm{THD_DAT_MIN}= \lceil{t\_{HD,DAT,min}/t\_{clk}}\rceil $$
$$ \textrm{TSU_DAT_MIN}= \lceil{t\_{HD,DAT,min}/t\_{clk}}\rceil $$
$$ \textrm{T_BUF_MIN}= \lceil{t\_{BUF,min}/t\_{clk}}\rceil $$
$$ \textrm{T_STO_MIN}= \lceil{t\_{STO,min}/t\_{clk}}\rceil $$

1. Input the integer timing parameters, THD_STA_MIN, TSU_STA_MIN, THD_DAT_MIN, TSU_DAT_MIN, T_BUF_MIN and T_STO_MIN into their corresponding registers (`TIMING2.THD_STA`, `TIMING2.TSU_STA`, `TIMING3.THD_DAT`, `TIMING3.TSU_DAT`, `TIMING4.T_BUF`, `TIMING4.T_STO`)
    - This step allows the firmware to manage SDA signal delays to ensure that the SDA outputs are compliant with the specification.
    - The registers `TIMING0.THIGH` and `TIMING0.TLOW` will be taken care of in a later step.
1. Take the given values for t<sub>f</sub> and t<sub>r</sub> and convert them to integer counts as well:
$$ \textrm{T_R}= \lceil{t\_{r}/t\_{clk}}\rceil $$
$$ \textrm{T_F}= \lceil{t\_{f}/t\_{clk}}\rceil $$
1. Store T_R and T_F in their corresponding registers: `TIMING1.T_R` and `TIMING1.T_F`.
1. Based on the input speed mode, look up the maximum permissible SCL frequency (f<sub>SCL,max</sub>)and calculate the minimum permissible SCL period:
$$ t\_{SCL,min}= 1/f\_{SCL,max} $$
1. As with each of the other physical parameters convert t<sub>SCL,min</sub> and, if provided, the t<sub>SCL,user</sub> to integers, MINPERIOD and USERPERIOD..
$$ MINPERIOD = \lceil{t\_{SCL,min}/t\_{clk}}\rceil $$
$$ USERPERIOD = \lceil{t\_{SCL,user}/t\_{clk}}\rceil $$
1. Let `PERIOD = max(MINPERIOD, USERPERIOD)`.
1. Each SCL cycle will now be at least `PERIOD` clock cycles in duration, divided between four segments: `T_R`, `THIGH`, `T_F`, and `TLOW`.
    - In other words: `PERIOD = T_R + THIGH + T_F + TLOW`.
    - With `T_R` and `T_F` already established, the remaining integer parameters `THIGH` and `TLOW` are to be divided among the remaining clock cycles in `PERIOD`:
$$ \textrm{THIGH}+\textrm{TLOW} \ge\textrm{PERIOD}-\textrm{T_F}-\textrm{T_R} $$
    - Since t<sub>HIGH</sub> and t<sub>LOW</sub> both have minimum allowable values, which depends on the mode, high values of t<sub>r</sub> or t<sub>f</sub> may force an increase in the total SCL period, slowing down the data transit rate.
    - The balance between t<sub>HIGH</sub> and t<sub>LOW</sub> can be manipulated in a variety of different ways (depending on the desired SCL duty cycle).
    - It is, for instance, perfectly acceptable to simply set TLOW to the minimum possible value:
$$ \textrm{TIMING0.TLOW}=\textrm{TLOW_MIN} $$
1. THIGH is then set to satisfy both constraints in the desired SCL period and in the minimum permissible values for t<sub>HIGH</sub>:
$$ \textrm{TIMING0.THIGH}=\max(\textrm{PERIOD}-\textrm{T_R} - \textrm{TIMING0.TLOW} -\textrm{T_F}, \textrm{THIGH_MIN}) $$


#### Timing parameter examples

The following tables show a couple of examples for calculating timing register parameters for Fast-mode Plus devices.
Both examples assume a desired datarate of 1 Mbaud (the bus maximum) for an SCL period of 1 us, and an internal device clock period of 3 ns.

| Parameter       | Spec. Min. (ns)  | Reg. Val.  | Phys. Val (ns) | Comment                                         |
|-----------------|------------------|------------|----------------|-----------------------------------------------|
| TIMING0.THIGH   | 260              | 120        | 360            | Chosen to satisfy SCL Period Minimum          |
| TIMING0.TLOW    | 500              | 167        | 501            | Spec. t<sub>LOW</sub> Minimum                 |
| TIMING1.T_F     | 20ns * (VDD/5.5V)| 7          | 21             | Signal slew-rate should be controlled         |
| TIMING1.T_R     | 0                | 40         | 120            | Based on pull-up resistance, line capacitance |
| SCL Period      | 1000             | N/A        | 1002           | Constraint on THIGH+TLOW+T_R+T_F              |
| TIMING2.THD_STA | 260              | 87         | 261            | Spec. Minimum                                 |
| TIMING2.TSU_STA | 260              | 87         | 261            | Spec. Minimum                                 |
| TIMING3.THD_DAT | 0                | 0          | 0              | Spec. Minimum                                 |
| TIMING3.TSU_DAT | 260              | 87         | 261            | Spec. Minimum                                 |
| TIMING4.T_BUF   | 500              | 167        | 501            | Spec. Minimum                                 |
| TIMING4.T_STO   | 260              | 87         | 161            | Spec. Minimum                                 |

This next example shows how the first SCL timing registers: `TIMING0` and `TIMING1` are altered in a high-capacitance Fast-mode Plus bus, where the physical value of t<sub>r</sub> driven to an atypical value of 400ns.
As in the previous example the integer register values are determined based on a system clock period, t<sub>clk</sub>, of 3ns.
All other parameters in registers `TIMING2`, `TIMING3`, `TIMING4` are unchanged from the previous example.

| Parameter       | Spec. Min. (ns)  | Reg. Val.  | Phys. Val (ns) | Comment                                       |
|-----------------|------------------|------------|----------------|-----------------------------------------------|
| TIMING0.THIGH   | 260              | 87         | 261            | Spec. t<sub>HIGH</sub> Minimum                |
| TIMING0.TLOW    | 500              | 167        | 501            | Spec. t<sub>LOW</sub> Minimum                 |
| TIMING1.T_F     | 20ns * (VDD/5.5V)| 7          | 21             | Signal slew-rate should be controlled         |
| TIMING1.T_R     | 0                | 134        | 402            | Atypically high line capacitance             |
| SCL Period      | 1000             | N/A        | 395            | Forced longer than minimum by long T_R        |

## Writing `n` bytes to a device:
1. Address the device for writing by writing to:
   - `FDATA.START` = 1;
   - `FDATA.FBYTE` = <7-bit address + write bit>.
2. Fill the TX_FIFO by writing to `FDATA.FBYTE` `n`-1 times.
3. Send last byte with the stop bit by writing to:
    - `FDATA.STOP` = 1;
    - `FDATA.FBYTE` = <last byte>.

<!-- TODO: Fix #18917 and remove the FMT_FIFO empty check before adding the full transaction to the FMT_FIFO -->
## Reading `n` bytes from a device:
1. Address the device for reading by writing to:
   - `FDATA.START` = 1;
   - `FDATA.FBYTE` = <7-bit address + read bit>.
2. Wait the write transaction to finish by either checking:
    - If `STATUS.FMTEMPTY` bit is 1.
    - **Or** if `INTR_STATE.fmt_threshold` bit is 1 ( as long as `FIFO_CTRL.FMTILVL` is set to 1).
3. If `INTR_STATE.nak` bit is 1, then go back to step 1, else proceed.
4. Issue a read transaction by writing to.
    - `FDATA.READ` = 1;
    - `FDATA.STOP` = 1;
    - `FDATA.FBYTE` = <`n`>.
5. Wait for the read transaction to finish by checking:
    -  `STATUS.FMTEMPTY` bit is 1.
6. Retrieve the data from the FIFO by reading `RDATA` `n` times.

## Device Interface Functions (DIFs)

- [Device Interface Functions](../../../../sw/device/lib/dif/dif_i2c.h)

## Register Table

* [Register Table](../data/i2c.hjson#registers)
