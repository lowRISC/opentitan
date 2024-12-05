# Analog Sensor Top Technical Specification
# Overview

AST, also known as the analog sensor top, is the OpenTitan analog and
security companion. Within AST are various analog functions (such as
clocks, regulators, random number generators) needed to make the device
function, as well as physical security sensors necessary to protect the
device from physical attacks or manipulation.

At a high level, AST communicates with a number of OpenTitan comportable
modules. See diagram below.

![Analog Sensor Top Diagram](./doc/top_diagram.png)

In the following sections, each family of connection is briefly
described and explained. Note, the analog connections to AST are not
shown in the diagram, but will be explained as well.

# Interface Signals Table

## Table notes

### Signal naming conventions used in this document

It complies with OpenTitan
[<u>names</u>](https://github.com/lowRISC/style-guides/blob/master/VerilogCodingStyle.md#naming)
and
[<u>suffixes</u>](https://github.com/lowRISC/style-guides/blob/master/VerilogCodingStyle.md#suffixes)
with some augmentations.

- Clock signals start with clk_*

- Inputs and outputs are marked with *_i/o

- Analog signals are marked with *_a

- Non-core level signals are marked with *_h

- Dual and negative polarity signals are marked with *_p/n

### Clock domains column

- sys - system clock, mainly used for high performance and security
 modules. Up to 100MHz

- io - peripheral clock source, mainly used for peripherals and I/O
 related functionality. Up to 96MHz (divided by 4 by the clock
 manager)

- usb - USB module source clock. 48MHz

- aon - Always-on domain clock. The only active clock while chip is in
 deep-sleep power state, 200KHz

- async - when listed as async, it means it does not matter what domain
 drives the signal

- Input clocks: Each functional interface has a dedicated clock named
 after the interface.

<table>
<colgroup>
<col style="width: 20%" />
<col style="width: 4%" />
<col style="width: 7%" />
<col style="width: 7%" />
<col style="width: 59%" />
</colgroup>
<thead>
<tr class="even">
<td><strong>Signal Name &amp; Affiliation</strong></td>
<td><strong>I/O</strong></td>
<td><p><strong>Width/</strong></p>
<p><strong>Type/</strong></p>
<p><strong>Struct</strong></p></td>
<td><strong>Clock Domain</strong></td>
<td><strong>Description</strong></td>
</tr>
<tr class="odd">
<td colspan="5"><strong>Power Supplies</strong></td>
</tr>
<tr class="even">
<td>VCC</td>
<td>I</td>
<td></td>
<td></td>
<td><p>VCC is the main power supply. It is driven from an external
source and is used to power the internal VCMAIN and VCAON power
domains.</p>
<p>VCC must always be present when the device is functioning; VCC is
also used to power a number of pads that must be always on when the
device is functioning.</p></td>
</tr>
<tr class="odd">
<td>AVCC</td>
<td>I</td>
<td></td>
<td></td>
<td>Analog blocks power supply. AVCC and AGND are analog supply and
ground signals for the AST analog functions. They mainly serve for ADC
and USB clock functionality. AVCC is expected to be driven by the same
voltage regulator and have similar power availability as VCC. AVCC and
AGND have dedicated package balls/pins. In the future, package pins
sharing with VCC and GND may be considered based on post-silicon test
results.</td>
</tr>
<tr class="even">
<td>VCMAIN</td>
<td>O</td>
<td></td>
<td></td>
<td>Main core power, driven by internal capless voltage regulator</td>
</tr>
<tr class="odd">
<td>VCAON</td>
<td>O</td>
<td></td>
<td></td>
<td>Core voltage power for always-on domain (same voltage range as
VCMAIN)</td>
</tr>
<tr class="even">
<td>VIOA</td>
<td>I</td>
<td></td>
<td></td>
<td>IO supply, powering a set of pads. Unlike VCC, the IO supplies can
be turned off by external components and the device will continue to
function, the unpowered pads however, become inoperable.</td>
</tr>
<tr class="odd">
<td>VIOB</td>
<td>I</td>
<td></td>
<td></td>
<td>Same as VIOA, but for a different set of pads.</td>
</tr>
<tr class="even">
<td>GND</td>
<td>I</td>
<td></td>
<td></td>
<td>Ground</td>
</tr>
<tr class="odd">
<td>AGND</td>
<td>I</td>
<td></td>
<td></td>
<td>Analog ground (see AVCC for further details)</td>
</tr>
<tr class="even">
<td colspan="5"><strong>Power Control and Reset</strong></td>
</tr>
<tr class="odd">
<td>otp_power_seq_i</td>
<td>I</td>
<td>2</td>
<td>async</td>
<td>Contains the power sequencing signals coming from the OTP
macro.</td>
</tr>
<tr class="even">
<td>otp_power_seq_h_o</td>
<td>O</td>
<td>2</td>
<td>async</td>
<td>Contains the power sequencing signals going to the OTP macro
(<strong>VCC domain</strong>).</td>
</tr>
<tr class="odd">
<td>flash_power_down_h_o</td>
<td>O</td>
<td>1</td>
<td>async</td>
<td>Connected to flash (<strong>VCC domain</strong>). Used for flash
power management.</td>
</tr>
<tr class="even">
<td>flash_power_ready_h_o</td>
<td>O</td>
<td>1</td>
<td>async</td>
<td>Connected to flash (<strong>VCC domain</strong>). Used for flash
power management.</td>
</tr>
<tr class="odd">
<td><p>vcmain_pok</p>
<p>(aka vcmain_pok_o)</p></td>
<td>O</td>
<td>ast_pwst</td>
<td>async</td>
<td>Main core power-exist indication. Used by the OpenTitan power
manager to determine the state of the main digital supply during power
up and power down sequencing.</td>
</tr>
<tr class="even">
<td><p>vcaon_pok</p>
<p>(aka vcaon_pok_o)</p></td>
<td>O</td>
<td>ast_pwst</td>
<td>async</td>
<td>Always-on power-exist indication. Used by the OpenTitan power
manager for power-on reset root.</td>
</tr>
<tr class="odd">
<td><p>vioa_pok</p>
<p>(aka vioa_pok_o)</p></td>
<td>O</td>
<td>ast_pwst</td>
<td>async</td>
<td>VIOA power-exist indications. Used as a power-OK status signal.</td>
</tr>
<tr class="even">
<td><p>viob_pok</p>
<p>(aka viob_pok_o)</p></td>
<td>O</td>
<td>ast_pwst</td>
<td>async</td>
<td>VIOB power-exist indication. Used as a power-OK status signal.</td>
</tr>
<tr class="odd">
<td>por_ni</td>
<td>I</td>
<td>1</td>
<td>async</td>
<td>Power on reset input signal to AST. See <a
href="#resets"><u>Resets</u></a> section for further details</td>
</tr>
<tr class="even">
<td>main_pd_ni</td>
<td>I</td>
<td>1</td>
<td>aon</td>
<td>Power down enable for main core power<br />
0: main core power is down (deep-sleep state)<br />
1: main core power is up<br />
It may take up to 200 uS from this signal transition to power switching
completion by AST (not including boot time and so). Note that flash must
be prepared for power down before this signal is asserted.</td>
</tr>
<tr class="odd">
<td>main_env_iso_en_i</td>
<td>I</td>
<td>1</td>
<td>aon</td>
<td><p>Preliminary indication of VCMAIN isolation signal (main_iso_en)
assertion. It is used by AST logic to latch interface signals which may
no longer be valid after main_iso_en is active. This signal must be set
at least 30ns before main_iso_en is active and must remain active at
least 30ns after main_iso_en is no longer active.</p>
<p>Note that main_iso_en itself asserts ahead of main_pd_ni. ie, the
pwrmgr will set this signal to '1' before requesting the power be turned
off. Similar, on power-on, the isolation is only released after power is
restored and all powered off modules have been reset.</p></td>
</tr>
<tr class="even">
<td>ast_init_done_o</td>
<td>O</td>
<td>mubi4</td>
<td>tlul</td>
<td>When set, it indicates that the AST initialization was performed.
Note that this signal may not be set while the chip is in TEST* or RMA
lifecycle states.</td>
</tr>
<tr class="odd">
<td colspan="5"><strong>Clock Outputs</strong></td>
</tr>
<tr class="even">
<td>clk_src_sys_o</td>
<td>O</td>
<td>1</td>
<td>sys</td>
<td>100 MHz clock with jitter (main clock domain). Used as the main
system clock.</td>
</tr>
<tr class="odd">
<td>clk_src_sys_val_o</td>
<td>O</td>
<td>1</td>
<td>async</td>
<td>System clock valid. Used as "ack" signals for the <a
href="https://opentitan.org/book/hw/ip/pwrmgr"><u>power
manager</u></a></td>
</tr>
<tr class="even">
<td>clk_src_sys_en_i</td>
<td>I</td>
<td>1</td>
<td>aon</td>
<td>System clock enable.</td>
</tr>
<tr class="odd">
<td>clk_src_sys_jen_i</td>
<td>I</td>
<td>mubi4</td>
<td>async</td>
<td>System clock jitter enable</td>
</tr>
<tr class="even">
<td>clk_src_aon_o</td>
<td>O</td>
<td>1</td>
<td>aon</td>
<td>200 KHz clock for always-on domain.</td>
</tr>
<tr class="odd">
<td>clk_src_aon_val_o</td>
<td>O</td>
<td>1</td>
<td>async</td>
<td>aon clock valid</td>
</tr>
<tr class="even">
<td>clk_src_usb_o</td>
<td>O</td>
<td>1</td>
<td>usb</td>
<td>48 MHz clock for USB. To comply with USB full speed clock
specification, it supports frequency accuracy of +/-2500 ppm when
usb_ref_pulse_i is available and +/-3% otherwise. It may take up to 50
ms for this clock to reach the accuracy target from the time
'usb_ref_pulse_i' is available. USB clock calibration interface is
further detailed <a
href="https://opentitan.org/book/hw/ip/usbdev#clocking"><u>here</u></a>.</td>
</tr>
<tr class="odd">
<td>clk_src_usb_val_o</td>
<td>O</td>
<td>1</td>
<td>async</td>
<td>USB clock valid</td>
</tr>
<tr class="even">
<td>clk_src_usb_en_i</td>
<td>I</td>
<td>1</td>
<td>aon</td>
<td>USB clock enable</td>
</tr>
<tr class="odd">
<td>usb_ref_pulse_i</td>
<td>I</td>
<td>1</td>
<td>usb</td>
<td>USB reference pulse +/-500ppm. When valid, it is expected to pulse
for one usb clock cycle every 1ms.</td>
</tr>
<tr class="even">
<td>usb_ref_val_i</td>
<td>I</td>
<td>1</td>
<td>usb</td>
<td>USB reference valid. This bit serves as a valid signal for the
usb_ref_pulse_i signal. It is set to 1 after the first valid
usb_ref_pulse_i event is detected and remains high as long as
usb_ref_pulse_i continues to behave as expected (per usb_ref_pulse
description). Once usb_ref_pulse deviates from its expected behavior,
usb_ref_val_i immediately negates to 0 and remains 0 until after the
next valid usb_ref_val pulse.</td>
</tr>
<tr class="odd">
<td>clk_src_io_o</td>
<td>O</td>
<td>1</td>
<td>io</td>
<td>96 MHz clock with +/-3% frequency accuracy. Used for peripherals
that require a fixed frequency, for example SPI and UART</td>
</tr>
<tr class="even">
<td>clk_src_io_val_o</td>
<td>O</td>
<td>1</td>
<td>async</td>
<td>I/O and timer clock valid. Used as "ack" signals for the <a
href="https://opentitan.org/book/hw/ip/pwrmgr"><u>Power
manager</u></a>.</td>
</tr>
<tr class="odd">
<td>clk_src_io_en_i</td>
<td>I</td>
<td>1</td>
<td>aon</td>
<td>I/O and timer clock enable</td>
</tr>
<tr class="even">
<td>clk_src_io_48m_o</td>
<td>O</td>
<td>mubi4</td>
<td>aon</td>
<td>Clock frequency indicator. When set, it indicates that the
clk_src_io_o's frequency is 48 MHz; otherwise, it is 96 MHz.</td>
</tr>
<tr class="odd">
<td colspan="5"><strong>Clock &amp; Reset Inputs</strong></td>
</tr>
<tr class="even">
<td>clk_ast_adc_i</td>
<td>I</td>
<td>1</td>
<td>adc</td>
<td>ADC interface clock input</td>
</tr>
<tr class="odd">
<td>clk_ast_rng_i</td>
<td>I</td>
<td>1</td>
<td>rng</td>
<td>RNG interface clock input</td>
</tr>
<tr class="even">
<td>clk_ast_usb_i</td>
<td>I</td>
<td>1</td>
<td>usb</td>
<td>USB reference interface clock input</td>
</tr>
<tr class="odd">
<td>clk_ast_es_i</td>
<td>I</td>
<td>1</td>
<td>es</td>
<td>Entropy source interface clock input</td>
</tr>
<tr class="even">
<td>clk_ast_alert_i</td>
<td>I</td>
<td>1</td>
<td>alert</td>
<td>Alert interface clock input</td>
</tr>
<tr class="odd">
<td>clk_ast_tlul_i</td>
<td>I</td>
<td>1</td>
<td>tlul</td>
<td>TLUL bus interface clock input</td>
</tr>
<tr class="even">
<td>rst_ast_adc_ni</td>
<td>I</td>
<td>1</td>
<td>adc</td>
<td>ADC interface reset (active low)</td>
</tr>
<tr class="odd">
<td>rst_ast_rng_ni</td>
<td>I</td>
<td>1</td>
<td>rng</td>
<td>RNG interface reset (active low)</td>
</tr>
<tr class="even">
<td>rst_ast_usb_ni</td>
<td>I</td>
<td>1</td>
<td>usb</td>
<td>USB reference interface reset (active low)</td>
</tr>
<tr class="odd">
<td>rst_ast_es_ni</td>
<td>I</td>
<td>1</td>
<td>es</td>
<td>Entropy source interface reset (active low)</td>
</tr>
<tr class="even">
<td>rst_ast_alert_ni</td>
<td>I</td>
<td>1</td>
<td>alert</td>
<td>Alert interface interface reset (active low)</td>
</tr>
<tr class="odd">
<td>rst_ast_tlul_ni</td>
<td>I</td>
<td>1</td>
<td>tlul</td>
<td>TLUL bus reference interface reset (active low)</td>
</tr>
<tr class="even">
<td colspan="5"><strong>Register Access Interface</strong></td>
</tr>
<tr class="odd">
<td>tlul</td>
<td>I/O</td>
<td>tl_*</td>
<td>tlul</td>
<td>TLUL bus interface. Mainly used for configuration, calibration and
trimming. At boot time, data is copied from non-volatile storage into
AST registers by the SW boot entity. This interface has no further use
beyond this point. Runtime interaction with AST is performed by other
signals as described in this document.</td>
</tr>
<tr class="even">
<td colspan="5"><strong>Analog modules</strong></td>
</tr>
<tr class="odd">
<td>adc_a0_ai</td>
<td>I</td>
<td>awire</td>
<td>async</td>
<td>ADC analog input channels 0 to be measured.<br />
Signal type is awire (see ana_pkg.sv)</td>
</tr>
<tr class="even">
<td>adc_a1_ai</td>
<td>I</td>
<td>awire</td>
<td>async</td>
<td>ADC analog input channels 1 to be measured.<br />
Signal type is awire (see ana_pkg.sv)</td>
</tr>
<tr class="odd">
<td>adc_d_o</td>
<td>O</td>
<td>10</td>
<td>adc</td>
<td>ADC digital data</td>
</tr>
<tr class="even">
<td>adc_chnsel_i</td>
<td>I</td>
<td>2</td>
<td>adc</td>
<td>ADC input channel select (one hot). No more than one channel should
be selected at a time. Any change in 'adc_chnsel_i' value must go
through all '0'. Changing 'adc_chnsel_i' from '0' value to non-'0' value
starts an ADC conversion.</td>
</tr>
<tr class="odd">
<td>adc_d_val_o</td>
<td>O</td>
<td>1</td>
<td>adc</td>
<td>ADC digital data valid</td>
</tr>
<tr class="even">
<td>adc_pd_i</td>
<td>I</td>
<td>1</td>
<td>adc</td>
<td>ADC power down - for saving power during deep-sleep state between
measurements. When this signal is high, ADC module is in off state,
otherwise, it is in active state. For further description about adc_pd_i
usage, see ADC module description below.</td>
</tr>
<tr class="odd">
<td>entropy_req_o</td>
<td>O</td>
<td>edn_req</td>
<td>es</td>
<td>Request entropy from EDN</td>
</tr>
<tr class="even">
<td>entropy_rsp_i</td>
<td>I</td>
<td>edn_rsp</td>
<td>es</td>
<td>EDN entropy request acknowledgement and data.</td>
</tr>
<tr class="odd">
<td>rng_en_i</td>
<td>I</td>
<td>1</td>
<td>rng</td>
<td>Input from controller to enable RNG</td>
</tr>
<tr class="even">
<td>rng_fips_i</td>
<td>I</td>
<td>1</td>
<td>rng</td>
<td>Indicates that the AST RNG module is requested to output FIPS
SP-800-90B grade RNG bits. This may, but not necessarily affect
bit-rate. This bit is a placeholder. The use of this signal inside AST
is TBD.</td>
</tr>
<tr class="odd">
<td>rng_val_o</td>
<td>O</td>
<td>1</td>
<td>rng</td>
<td>RNG bit valid. This is a per-transaction valid. rng_b_o can be
sampled whenever this bit is high.</td>
</tr>
<tr class="even">
<td>rng_b_o</td>
<td>O</td>
<td>4</td>
<td>rng</td>
<td>RNG digital bit streams. The downstream controller of this signal
should sample the rng_b_o whenever rng_val_o is high.</td>
</tr>
<tr class="odd">
<td colspan="5"><strong>Countermeasures and Alerts</strong></td>
</tr>
<tr class="even">
<td>alert_req_o</td>
<td>O</td>
<td>ast_alert_req</td>
<td>alert</td>
<td>Alert events. There are 11 such events. The alerts are associated
with countermeasures like Active shield, clock glitch detector, voltage
glitch detector, temperature sensor, and others.</td>
</tr>
<tr class="odd">
<td>alert_rsp_i</td>
<td>I</td>
<td>ast_alert_rsp</td>
<td>alert</td>
<td>This structure contains acknowledge signals and force-trigger by
software signals for each alert event. The acknowledge signals are
assumed to be synchronous pulses.</td>
</tr>
<tr class="even">
<td colspan="4"><strong>Trimming Test and Debug</strong></td>
<td></td>
</tr>
<tr class="odd">
<td>dft_scan_md_o</td>
<td>O</td>
<td>mubi4</td>
<td></td>
<td>Scan mode indication signal. Controllable only when DFT features are
enabled (Test and RMA states). Otherwise, these signals are grounded to
0.</td>
</tr>
<tr class="even">
<td>scan_shift_en_o</td>
<td>O</td>
<td>1</td>
<td></td>
<td>Scan shift enable</td>
</tr>
<tr class="odd">
<td>scan_reset_no</td>
<td>O</td>
<td>1</td>
<td></td>
<td>Scan reset</td>
</tr>
<tr class="even">
<td>clk_ast_ext_i</td>
<td>I</td>
<td>1</td>
<td>async</td>
<td><p>External clock. While AST generates most of its clocks on-die, it
still needs an external clock for clock calibration and first flash/OTP
programming.</p>
<p>Clock calibration: AST clock sources are inaccurate by default and
must be calibrated prior to use. The results of the calibration are
stored in <a
href="https://opentitan.org/book/hw/ip/otp_ctrl"><u>OTP</u></a> and
reloaded by software upon system boot.</p>
<p>First Flash / OTP programming: AST clock sources are inaccurate by
default and may be out of range for initial flash and OTP programming.
In this situation, an external clock may be required for initial
programming such that a software image can be loaded to calibrate clocks
and advance <a
href="https://opentitan.org/book/doc/security/specs/device_life_cycle"><u>life
cycle</u></a>.</p></td>
</tr>
<tr class="odd">
<td>dft_strap_test_i</td>
<td>I</td>
<td>dft_strap_test_req</td>
<td>async</td>
<td>Strap inputs for DFT selection</td>
</tr>
<tr class="even">
<td>flash_bist_en_o</td>
<td>O</td>
<td>mubi4</td>
<td></td>
<td>Flash BIST enable</td>
</tr>
<tr class="odd">
<td>vcc_supp_i</td>
<td>I</td>
<td>1</td>
<td>async</td>
<td>VCC Supply Test. (supply indication for DV purposes). In FPGA
Verilog view, the respective POK signal follows this signal. In other
Verilog views this signal should be connected to constant '1' and will
be disconnected inside the AST.</td>
</tr>
<tr class="even">
<td>vcmain_supp_i</td>
<td>I</td>
<td>1</td>
<td>async</td>
<td>VCMAIN Supply Test. (supply indication for DV purposes). In FPGA
Verilog view, the respective POK signal follows this signal. In other
Verilog views this signal should be connected to constant '1' and will
be disconnected inside the AST.</td>
</tr>
<tr class="odd">
<td>vcaon_supp_i</td>
<td>I</td>
<td>1</td>
<td>async</td>
<td>VCAON Supply Test. (supply indication for DV purposes). In FPGA
Verilog view, the respective POK signal follows this signal. In other
Verilog views this signal should be connected to constant '1' and will
be disconnected inside the AST.</td>
</tr>
<tr class="even">
<td>vioa_supp_i</td>
<td>I</td>
<td>1</td>
<td>async</td>
<td>VIOA Supply Test. (supply indication for DV purposes). In FPGA
Verilog view, the respective POK signal follows this signal. In other
Verilog views this signal should be connected to constant '1' and will
be disconnected inside the AST.</td>
</tr>
<tr class="odd">
<td>viob_supp_i</td>
<td>I</td>
<td>1</td>
<td>async</td>
<td>VIOB Supply Test. (supply indication for DV purposes). In FPGA
Verilog view, the respective POK signal follows this signal. In other
Verilog views this signal should be connected to constant '1' and will
be disconnected inside the AST.</td>
</tr>
<tr class="even">
<td>ast2pad_t0_ao, ast2pad_t1_ao</td>
<td>I/O</td>
<td></td>
<td>async</td>
<td>Analog debug signals. These signals should be connected directly to
chip PADs. They can share PADs with functional signals but when they are
used for their analog debug function, the functional I/O must be in
tri-state.</td>
</tr>
<tr class="odd">
<td><p>dpram_rmf_o,</p>
<p>dpram_rml_o,</p>
<p>spram_rm_o,</p>
<p>sprgf_rm_o,</p>
<p>sprom_rm_o</p></td>
<td>O</td>
<td>dpm_rm</td>
<td>async</td>
<td>RAM/ROM Read-write Margin Trimming</td>
</tr>
<tr class="even">
<td>padmux2ast_i</td>
<td>I</td>
<td>6</td>
<td>async</td>
<td>Digital debug input signals (routed to pin mux). These signals are
controllable only when DFT features are enabled (Test and RMA states).
Otherwise, these signals are grounded to 0.</td>
</tr>
<tr class="odd">
<td>ast2padmux_o</td>
<td>O</td>
<td>9</td>
<td>async</td>
<td>Digital debug output signals (routed to pin mux). These signals are
only outputted when DFT features are enabled (Test and RMA states).
Otherwise, these signals are grounded to 0.</td>
</tr>
<tr class="even">
<td>usb_io_pu_cal_o</td>
<td>O</td>
<td>20</td>
<td>async</td>
<td>USB I/O calibration and trimming</td>
</tr>
<tr class="odd">
<td>io_clk_byp_req_i</td>
<td>I</td>
<td>mubi4</td>
<td>async</td>
<td><p>External clock mux override request for OTP bootstrap purposes.
AST responds to the request by setting io_clk_byp_ack_o to 'On'. When
this bit is set and ack was received, clk_ast_ext_i serves as the io_clk
clock root.</p>
<p>Note: When 'On' (after ack), clk_src_io_o clock max frequency is
limited to 50 MHz</p></td>
</tr>
<tr class="even">
<td>io_clk_byp_ack_o</td>
<td>O</td>
<td>mubi4</td>
<td>async</td>
<td>AST response to io_clk_byp_req_i. The ack is set to 'On' after clock
switching function is performed.</td>
</tr>
<tr class="odd">
<td>all_clk_byp_req_i</td>
<td>I</td>
<td>mubi4</td>
<td>async</td>
<td><p>External clock mux override request for OTP bootstrap purposes.
AST responds to the request by setting io_clk_byp_ack_o to 'On'. When
this bit is set and ack was received, clk_ast_ext_i serves as the io_clk
clock root.</p>
<p>Note: When 'On' (after ack), clk_src_io_o clock max frequency is
limited to 50 MHz</p></td>
</tr>
<tr class="even">
<td>all_clk_byp_ack_o</td>
<td>O</td>
<td>mubi4</td>
<td>async</td>
<td>AST response to io_clk_byp_req_i. The ack is set to 'On' after clock
switching function is performed.</td>
</tr>
<tr class="odd">
<td>ext_freq_is_96m_i</td>
<td>I</td>
<td>mubi4</td>
<td>async</td>
<td>External clock frequency indication to AST. When set, it indicates
that the external clock is 96MHz.</td>
</tr>
<tr class="even">
<td>lc_dft_en_i</td>
<td>I</td>
<td>lc_tx</td>
<td>async</td>
<td><p>DFT enable</p></td>
</tr>
<tr class="odd">
<td>fla_obs_i</td>
<td>I</td>
<td>8</td>
<td>async</td>
<td>Flash observe bus for debug</td>
</tr>
<tr class="even">
<td>otp_bos_i</td>
<td>I</td>
<td>8</td>
<td>async</td>
<td>OTP observe bus for debug</td>
</tr>
<tr class="odd">
<td>usb_obs_i</td>
<td>I</td>
<td>1</td>
<td>async</td>
<td>USB differential receiver output observe for debug</td>
</tr>
<tr class="even">
<td>otm_obs_i</td>
<td>I</td>
<td>8</td>
<td>async</td>
<td>OpenTitan modules observe bus for debug (optional)</td>
</tr>
<tr class="odd">
<td>obs_ctrl_o</td>
<td>O</td>
<td>ast_obs_ctrl</td>
<td>async</td>
<td>Observability control structure. It contains observability module
selection, signal group selection and enable logic. Open source modules
may choose to use this infrastructure for selecting and gating
observability signals to be driven into otm_obs_i bus. Whether to
actually use this interface or not for open source modules observability
is a project decision.</td>
</tr>
<tr class="even">
<td>sns_clks_i</td>
<td>I</td>
<td>clkmgr_out</td>
<td>async</td>
<td>Clocks observability</td>
</tr>
<tr class="odd">
<td>sns_rst_i</td>
<td>I</td>
<td>rstmgr_out_t</td>
<td>async</td>
<td>Resets observability</td>
</tr>
<tr class="even">
<td>sns_spi_ext_clk_i</td>
<td>I</td>
<td>1</td>
<td>async</td>
<td>SPI external clock observability</td>
</tr>
</thead>
<tbody>
</tbody>
</table>

# Interfaces Description Note

The information below augments the [<u>Interface Signals
Table</u>](#interface-signals-table). For further details, see the
corresponding signals description in the table.

# Power Connectivity

Note: Power signals may not appear in the verilog files, however, they
are described for completeness.

## External Supplies

AST has four external power supplies VCC, AVCC, VIOA and VIOB. VCC is
the main supply, AVCC is an analog VCC supply. VIOA and VIOB are two
additional I/O supplies.

## Core Supplies

The core supplies are generated from the VCC supply. There are two core
supply domains: VCMAIN and VCAON. VCAON, as its name implies, is the
always-on core supply used to power components that stay active during
device low power states. VCMAIN on the other hand, powers most chip
logic such as RISC-V processor, crypto modules and almost all memories
and peripherals. The VCMAIN supply can be turned off when requested,
VCAON on the other hand, is active whenever VCC is active. AST core
logic is powered by VCAON.

# Power Control and Reset

## Core Power Control and Indication

VCMAIN is the only supply that can be directly influenced by OpenTitan.
The power manager can request VCMAIN to shutdown through main_pd_ni. The
state of VCMAIN is reflected by the vcmain_pok_o signal.

## IO Power Indication

IO power state is reflected to OpenTitan by vioa_pok_o and viob_pok_o
signals

## Main (VCC) Power Detection and Flash Protection

On VCC power-down detection, 'flash_power_ready_h_o', is
immediately negated. In addition, SYS clock, IO clock and USB clock are
stopped. This means that negation of the VCC supply always triggers the
flash brown-out (BOR) protection circuitry.

When entering deep-sleep mode, 'flash_power_down_h_o' is
asserted before negating VCMAIN until VCMAIN is back up.

## Resets

The AST supports the generation of the root reset for the reset manager.
It is driven by 'vcaon_pok_o' which is generated inside AST.
The 'vcaon_pok_o' is activated when the following conditions
are met: VCC is detected, internal voltage regulator is active and
'por_ni' reset input is inactive. 'por_ni' is
driven by an external chip reset pin. The following table and diagrams
describe the AST sub-modules resets.

| **Components**                                               | **Reset by**             | **Comments**                                                                                                                             |
|--------------------------------------------------------------|--------------------------|------------------------------------------------------------------------------------------------------------------------------------------|
| Regulators, 'power-OK' logic and always-on clock | self-start / vcaon_pok_o | These circuits come to life shortly after VCC crosses its detection threshold. vcaon_pok_o serves as their register configuration reset. |
| System/USB/IO clock generators                               | vcmain_pok_o             | vcmain_pok_o is also fed by vcaon_pok_o and por_ni.                                                                                      |
| Interface functions                                          | Input reset              | Per the corresponding interface [<u>clock domain reset input</u>](#clock-and-reset-inputs).                                                  |

# Clock Outputs

AST generates four clocks: System clock, IO clock, USB clock and
Always-on clock. Most clocks have 'enable' inputs and a
corresponding 'valid' output. When the enable is
de-asserted, the corresponding clock stops and valid is dropped to 0.
When the enable is asserted, the clocks begin outputting in a
'glitchless' manner and the valid is raised to 1. Unless
noted otherwise, clocks duty cycle is 50% +/-5%. At boot time, clocks
start toggling at a different (typically slower) frequency than their
target. They are configured to their target frequency by the ROM code.
Once configured, their frequency is maintained within +/-3% of their
target as long as the chip remains in its intended operating conditions
until the next boot.

The OpenTitan power and clock managers are responsible for manipulating
the enables and observing the valids to know when clocks can be safely
released to the system.

## USB Clock Calibration

The USB clock requires an accuracy that cannot be achieved by the AST
clocks natively. As a result, information from USB frames are used to
[<u>calibrate the
clock</u>](../../../ip/usbdev/README.md#clocking).

# Clock and Reset Inputs

The root clocks and resets are generated inside AST. However, the clocks
go through gating and optional division in the OpenTitan top level and
propagate back into AST as feedback clocks, each with associated
synchronized reset de-assertion to ensure it can synchronize with the
various comportable modules. The input resets are used for the different
AST interface functions. For further details about AST resets, see
[<u>Resets</u>](#resets) section.

Note: There are several reasons for routing leaf clocks back into AST
instead of using the root clocks directly

- The leaf clocks may be divided down from the root clock and that
 frequency is used to drive the interface. For example,
 clk_src_io_clk_o is 96MHz, but comportable modules use either 48MHz
 or 24MHz.

- The leaf clocks and root clocks have very different clock tree depths
 and may be difficult for timing closure if they interacted directly.

- Decouple AST internal design from OpenTitan top-level interfaces clock
 and reset selection.

# Register Access Interface

AST registers can be accessed via TL-UL interface. These registers are
used for test and calibration purposes and are not required for runtime
operation. See the [<u>Interface Signals
Table</u>](#interface-signals-table) for more details.

## AST registers initialization during boot.

In PROD*/DEV Lifecycle states, the ROM code must copy all AST REGA
registers values from OTP to AST. During other Lifecycle states, the ROM
code may also copy all AST REGA registers. It is recommended for the
ROM code to condition the copy by a digest verification of the register
values. If such a digest is too complicated, a simple tag can be used to
condition the copy instead. The AST register copy operation must be
performed in order and must include all REGA registers (starting from
REGA0 and ending at the last REGA). AST sets the ast_init_done_o signal
after the copy completion.

After the copy, ROM code can either poll for ast_init_done_o assertion
with 100 us timeout (in practice, it should take way less) or ignore it
and let the next SW layers handle it. It is recommended to set an OTP
field for determining the ROM code action.

The boot code is expected to check all AST output alert signals before
handing over the control to the next code layer (ROM_EXT). The ROM code
response per alert should be defined in a dedicated OTP space.
Recommended response types (per alert):

1.  Do nothing and don't clear the event

2.  Do nothing (continue to the next SW layer) and clear the event

3.  Log the event in some NV space and halt

4.  Halt immediately

Note that in TEST_UNLOCK*/RMA state, the booter should always act per
#1 regardless of the OTP setting.

It is recommended to redundantly code the OTP fields that control the
ROM code branching and also to protect the branching code from fault
injection.

# ADC

AST contains an analog to digital converter that can be used to sample
various input signals. For OpenTitan this will primarily be used for
[<u>debug cable detection</u>](https://www.sparkfun.com/products/14746).
To activate the ADC, the corresponding [<u>comportable
module</u>](../../../ip/adc_ctrl/README.md) must first
activate the ADC through 'adc_pd_i'. Once activated, it should select
the channel to sample. Channel transition from zero to non-zero value
starts the ADC conversion. The ADC output is synchronous to the ADC
controller.

## ADC Usage Flow

1.  Activate the ADC by negating 'adc_pd_i'

2.  Wait 30 uS for the ADC to wake up.

3.  Select an analog channel to measure by setting the corresponding bit
 in 'adc_chnsel_i' bus. This triggers a measurement.

4.  Wait until 'adc_d_val' is set and read the result via
 'adc_d_o'

5.  Clear 'adc_chnsel_i' bus to 0. Note that adc_chnsel must
 be cleared to 0 before a new channel is selected.

6.  Repeat steps 3-5 if more channels or more measurements are required

7.  Deactivate the ADC by setting 'adc_pd_i' to save power.

```wavejson
{ signal: [ {node: '.a..b........', phase:0.2},
{name: 'adc_pd_i' , wave: '10|..|.....|....|..1'}, {name:
'clk_ast_adc_i', wave: 'p.|..|.....|....|...'}, {name:
'adc_chnsel_i' , wave: '0.|.3|..04.|....|0..'}, {name:
'adc_d_val_o' , wave: '0.|..|.1.0.|.1..|.0.'}, {name: 'adc_d_o' ,
wave: 'x.|..|.3.x.|.4..|.x.', data: ['ch0', 'ch1', 'ch1']}, ],
edge: [ 'a<->b wakeup time', ] }
```

# Random Number Generator

AST contains an entropy source vendor IP block that generates random number
bitstreams, and performs health testing and conditioning of these random
numbers. The conditioned and FIPS compliant entropy bits are packed into
384-bit seeds and then fed into the [<u>OpenTitan CSRNG
module</u>](../../../ip/csrng/README.md).


# Entropy Consumption

AST consumes entropy for defensive purposes. However, AST does not
consume its raw entropy directly. Instead, AST receives entropy from the
[<u>Entropy Distribution Network
(EDN)</u>](../../../ip/edn/README.md). Note
that entropy_ack and entropy_i are packed into enropy_rsp_i in the
interface. Also note that once entropy_req_o is set, it will remain set
until ack or until reset.

```wavejson
{signal: [

{name: 'clk_ast_es_i' , wave: 'p.|..........'},

{name: 'entropy_req_o' , wave: '01|.0.1.....0'},

{name: 'entropy_ack_i' , wave: '0.|10.1.01..0'},

{name: 'entropy_i' , wave: 'xx|2x.22x222x'},

] }
```

# Countermeasures and Alerts

## Alert Events

AST's sensors and detectors, when triggered, output alert events
to a sensor controller. The event signals are level until acknowledged
by the controller. Further, the events are differentially encoded to
ensure they cannot be hard-wired or faulted to either '1' or
'0'.

<!---
Inside the sensor controller, the events are then converted into alerts
as part of the wider [<u>OpenTitan alert handling
system</u>](../../ip_autogen/alert_handler/README.md).
--->

## Alert Signaling

Outgoing alert events are level. Incoming event ack signals clear the
alert event (similar to an interrupt). Outgoing alert events should be
OR'd inside the sensor or power manager (depending on what level of deep
sleep support is needed) to generate wakeup, that way AST does not need
to do any additional handling for wakeups during low power mode.

The AST defines each alert signal in both positive (P) and negative (N)
polarity (see ast_dif_t typedef with 'p' and 'n'
signals), however, the P and N signals are not necessarily fully
differential, for example, at times, it might occur that both P and N
are at the same value. For alert_o case, the correct way to treat it is
to propagate an alert signal if either P is high or N is low.

## Countermeasures

Most countermeasure enablement is controlled by Nuvoton via the
registers interface. Clock jitter is an exception because there is a
reasoning for dynamically turning it on and off (security/performance
tradeoff). Unless stated otherwise, countermeasures are active in all
modes but deep-sleep.
