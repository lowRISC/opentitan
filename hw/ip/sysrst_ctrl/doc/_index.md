---
title: "System Reset Control Technical Specification"
---

# Overview

This document specifies the functionality of the System Reset Controller (`sysrst_ctrl`) that provides programmable hardware-level responses to trusted IOs and basic board-level reset sequencing capabilities.
These capabilities include keyboard and button combination-triggered actions, reset stretching for system-level reset signals, and internal reset / wakeup requests that go to the OpenTitan reset and power manager blocks.
This module conforms to the [Comportable guideline for peripheral functionality.]({{< relref "doc/rm/comportability_specification" >}}).
See that document for integration overview within the broader top level system.

## Features

The IP block implements the following features:

- Always-on: uses the always-on power and clock domain
- EC reset pulse duration control and stretching
- Keyboard and button combination (combo) triggered action
- AC_present can trigger interrupt
- Configuration registers can be set and locked until the next chip reset
- Pin output override

## Description

The `sysrst_ctrl` logic is very simple.
It looks up the configuration registers to decide how long the EC reset pulse duration and how long the keyboard debounce timer should be.
Also what actions to take (e.g. Interrupt, EC reset, OpenTitan reset request, disconnect the battery from the power tree).

## Compatibility

The configuration programming interface is not based on any existing interface.

# Theory of Operations

![`sysrst_ctrl` Block Diagram](sysrst_ctrl_blockdiagram.svg)

The block diagram above shows a conceptual view of the `sysrst_ctrl` block, which consists of 3 main modules:
The first is the configuration and status registers, the second is the keyboard combo debounce and detection logic, and the third is the pinout override logic.

The `sysrst_ctrl` has four input pins (`pwrb_in_i`, `key[0,1,2]_in_i`) with corresponding output pins (`pwrb_out`, `key[0,1,2]_out`).
During normal operation the `sysrst_ctrl` will pass the pin information directly from the input pins to the output pins with optional inversion.
Combinations of the inputs being active for a specified time can be detected and used to trigger actions.
The override logic allows the output to be overridden (i.e. not follow the corresponding input) based either on trigger or software settings.
This allows the security chip to take over the inputs for its own use without disturbing the main user.

The `sysrst_ctrl` also controls two active-low open-drain I/Os named `flash_wp_l_i` / `flash_wp_l_o` and `ec_rst_l_i` / `ec_rst_l_o`.
The `ec_rst_l_i` / `ec_rst_l_o` signals are connected to the same bidirectional pin of the OpenTitan chip, and are used to either reset the embedded controller (EC), or to detect self-reset of the EC and stretch the reset pulse (hence the bidirectional nature of this pin).
This output is always asserted when `sysrst_ctrl` is reset (allowing its use as a power-on reset) and remains asserted until released by software.
The flash write-protect output `flash_wp_l_o` is typically connected to the BIOS flash chip in the system.
This output is always asserted when the `sysrst_ctrl` block is reset and remains asserted until released by software.

## Hardware Interfaces

{{< incGenFromIpDesc "../data/sysrst_ctrl.hjson" "hwcfg" >}}

## Combo detection

Software can program the `sysrst_ctrl` block to detect certain button combos and for how long they have to be asserted until they trigger a programmable action.
Let's use the "Power button + Esc + Refresh" combo as an example:

1. Software can define the three key values `pwrb_in_i==0`, `key0_in_i==0` and `key1_in_i==0` as trigger combination in the {{< regref COM_SEL_CTL_0 >}} register.
2. The combo duration for which the above combo should be pressed (e.g. 10 seconds) can be configured via the {{< regref COM_DET_CTL_0 >}} register.
3. Actions such as asserting `ec_rst_l_o` and raising an interrupt can be configured via the {{< regref COM_OUT_CTL_0 >}} register.
4. The pulse width of the `ec_rst_l_o` pulse can be set in the {{< regref EC_RST_CTL >}} register.
5. The software can optionally lock the `sysrst_ctrl` configuration via {{< regref REGWEN >}}

Once the above configuration is active, `sysrst_ctrl` will start the timer when a combo high (logic 1) to low (logic 0) transition is detected.
Once the timing condition is met (10 seconds), `sysrst_ctrl` will assert `ec_rst_l_o`, the interrupt request and set the interrupt status register {{< regref COMBO_INTR_STATUS >}} to indicate the interrupt cause.
The software interrupt handler should then read the {{< regref COMBO_INTR_STATUS >}} register and clear the interrupt via the {{< regref INTR_STATE >}} register.

Note that an interrupt will also issue a wakeup request to the OpenTitan power manager via `wkup_req_o`.
Software should therefore read and clear the {{< regref WKUP_STATUS >}} register as well.

### Combo actions

The following four combo actions can be triggered:

- Drive the `bat_disable` output high until the next reset.
- Issue an interrupt to the processor via `intr_event_detected_o`.
- Assert `ec_rst_l_o` for the amount of cycles configured in {{< regref EC_RST_CTL >}}.
- Issue a reset request via `rst_req_o` to the reset manager of the OpenTitan system. Note that once a reset request is issued, it will remain asserted until the next reset.

These actions can be configured via the {{< regref COM_OUT_CTL_0 >}} register for each of the combo blocks as described in the previous section.

### Hardwired reset stretching functionality

In addition to the combo action described above, `ec_rst_l_o` is automatically asserted for the amount of cycles defined in the {{< regref EC_RST_CTL >}} register whenever the `ec_rst_l_i` input is asserted (i.e., when it transitions from high to low).

## Auto-block key outputs

Software can program the `sysrst_ctrl` block to override the output value of specific passthrough signals, depending on whether certain input signals are asserted or not.
Let's use the "Power button + Esc + Refresh" combo as an example.
When `pwrb_in_i` is asserted, `key1_out_o` (row) should be overridden so that `sysrst_ctrl` can detect if `key0_in_i` (column) is Refresh.

1. The software enables the auto block feature and sets an appropriate debounce timer value in the {{< regref AUTO_BLOCK_DEBOUNCE_CTL >}} register.
2. The software then defines the key outputs to auto override and their override values in the {{< regref AUTO_BLOCK_OUT_CTL >}} register.

Once the above configuration is active, `sysrst_ctrl` will detect a high (logic 1) to low (logic 0) transition on `pwrb_in_i` and check whether the key `pwrb_in_i` stays low for the programmed duration.
If this condition is met, `sysrst_ctrl` will drive `key1_out_o` to the value programmed in {{< regref AUTO_BLOCK_OUT_CTL >}}.

## Keyboard and input triggered interrupt

Software can program the `sysrst_ctrl` block to detect edge transitions on the `pwrb_in_i`, `key0_in_i`, `key1_in_i`, `key2_in_i`, `ac_present_i`, `ec_rst_l_i` and `flash_wp_l_i` signals and trigger an interrupt:

1. Software first defines the input signal and the edge transition to detect (H->L or L->H) via the {{< regref KEY_INTR_CTL >}} register.
2. The software then programs an appropriate debounce timer value to the {{< regref KEY_INTR_DEBOUNCE_CTL >}} register.

For example, when the power button is pressed, `pwrb_in_i` goes from logic 1 to logic 0 which would amount to an H->L transition.
Likewise, when the power button is released, `pwrb_in_i` goes from logic 0 to logic 1 which would amount to an L->H transition.
When `sysrst_ctrl` detects a transition (H->L or L->H) as specified in {{< regref KEY_INTR_CTL >}} and it meets the debounce requirement in {{< regref KEY_INTR_DEBOUNCE_CTL >}}, `sysrst_ctrl` sets the {{< regref KEY_INTR_STATUS >}} register to indicate the interrupt cause and send out a consolidated interrupt to the PLIC.
The software interrupt handler should then read the {{< regref KEY_INTR_STATUS >}} register and clear the interrupt via the {{< regref INTR_STATE >}} register.

Note that an interrupt will also issue a wakeup request to the OpenTitan power manager via `wkup_req_o`.
Software should therefore read and clear the {{< regref WKUP_STATUS >}} register as well.

## Ultra-low-power Wakeup Feature

Software can program the `sysrst_ctrl` block to detect certain specific signal transitions on the (possibly inverted) `ac_present_i`, `pwrb_in_i` and `lid_open_i` inputs.
As opposed to the combo detection and general key interrupt features above, this is a fixed function feature with limited configurability.
In particular, the transitions that can be detected are fixed to the following:

- A high level on the `ac_present_i` signal
- A H -> L transition on the `pwrb_in_i` signal
- A L -> H transition on the `lid_open_i` signal

Note that the signals may be potentially inverted due to the [input inversion feature]({{< relref "#inversion" >}}).

In order to activate this feature, software should do the following:

1. Software can program the appropriate debounce times via the {{< regref ULP_AC_DEBOUNCE_CTL >}}, {{< regref ULP_LID_DEBOUNCE_CTL >}} and {{< regref ULP_PWRB_DEBOUNCE_CTL >}} registers.
2. Then, software can activate detection by setting the {{< regref ULP_CTL >}} register to 1.

Once the above configuration is active, `sysrst_ctrl` will start the timer when a transition is detected.
Once the timing condition is met, `sysrst_ctrl` will assert `z3_wakeup` output signal, the interrupt request and set the interrupt status register {{< regref ULP_STATUS >}} to indicate the interrupt cause.
The software interrupt handler should then read the {{< regref ULP_STATUS >}} register and clear the interrupt via the {{< regref INTR_STATE >}} register.

Note that an interrupt will also issue a wakeup request to the OpenTitan power manager via `wkup_req_o`.
Software should therefore read and clear the {{< regref WKUP_STATUS >}} register as well.

Also note that the detection status is sticky.
I.e., software needs to explicitly disable this feature by setting {{< regref ULP_CTL >}} to 0 in order to clear the FSM state.
If software wants to re-arm the mechanism right away, it should first read back {{< regref ULP_CTL >}} to make sure it has been cleared before setting that register to 1 again.
This is needed because this register has to be syncronized over to the AON clock domain.

## Pin input value accessibility

`sysrst_ctrl` allows the software to read the raw input pin values via the {{< regref PIN_IN_VALUE >}} register like GPIOs.
To this end, the hardware samples the raw input values of `pwrb_in_i`, `key[0,1,2]_in_i`, `ac_present_i`, `ec_rst_l_i`, `flash_wp_l_i` before they are being inverted, and synchronizes them onto the bus clock domain.

## Pin output and keyboard inversion control {#inversion}

Software can optionally override all output signals, and change the signal polarity of some of the input and output signals.
The output signal override feature always has higher priority than any of the combo pattern detection mechanisms described above.

The selection of output signals to override, and the override values are programmable and lockable via the {{< regref PIN_ALLOWED_CTL >}} register.
For example, {{< regref PIN_ALLOWED_CTL.EC_RST_L_0 >}} to 1 and {{< regref PIN_ALLOWED_CTL.EC_RST_L_1 >}} to 0 means that software allows `ec_rst_l_o` to be overridden with logic 0, but not with logic 1.
If the SW locks the configuration with {{< regref REGWEN >}}, {{< regref PIN_ALLOWED_CTL >}} cannot be modified until the next OpenTitan reset.

When the system is up and running, the software can modify {{< regref PIN_OUT_CTL >}} and {{< regref PIN_OUT_VALUE >}} to enable or disable the feature.
For example, to release `ec_rst_l_o` after OpenTitan completes the reset, software can set {{< regref PIN_OUT_CTL >}} to 0 to stop the hardware from driving `ec_rst_l_o` to 0.

The input / output signal inversions can be programmed via the {{< regref KEY_INVERT_CTL >}} register.
Input signals will be inverted before the combo detection logic, while output signals will be inverted after the output signal override logic.

## EC and Power-on-reset

OpenTitan and EC will be reset together during power-on.
When OpenTitan is in reset, `ec_rst_l_o` will be asserted (active low).
The power-on-reset value of {{< regref PIN_ALLOWED_CTL.EC_RST_L_1 >}} and {{< regref PIN_OUT_CTL.EC_RST_L >}} will guarantee that `ec_rst_l_o` remains asserted after OpenTitan reset is released.
The software can release `ec_rst_l_o` explicitly by setting {{< regref PIN_OUT_CTL.EC_RST_L >}} to 0 during boot in order to complete the OpenTitan and EC power-on-reset sequence.

Note that since the `sysrst_ctrl` does not have control over the pad open-drain settings, software should properly initialize the pad attributes of the corresponding pad in the [pinmux configuration]({{< relref "hw/ip/pinmux/doc/" >}}) before releasing `ec_rst_l_o`.

## Flash Write Protect Output

Upon reset, the `flash_wp_l_o` signal will be asserted active low.
The software can release `flash_wp_l_o` explicitly by setting {{< regref PIN_OUT_CTL.FLASH_WP_L >}} to 0 when needed.
The `flash_wp_l_o` signal does have a corresponding input signal `flash_wp_l_i` - but that one is mainly intended for pad observability and does not have a bypass path to `flash_wp_l_o`.
Hence, the value of `flash_wp_l_o` defaults to logic 0 when it is not explicitly driven via the override function.

Note that since the `sysrst_ctrl` does not have control over the pad open-drain settings, software should properly initialize the pad attributes of the corresponding pad in the [pinmux configuration]({{< relref "hw/ip/pinmux/doc/" >}}) before releasing `flash_wp_l_o`.

## Device Interface Functions (DIFs)

{{< dif_listing "sw/device/lib/dif/dif_sysrst_ctrl.h" >}}

## Registers

{{< incGenFromIpDesc "../data/sysrst_ctrl.hjson" "registers" >}}
