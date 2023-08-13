# Theory of Operation

![`sysrst_ctrl` Block Diagram](./sysrst_ctrl_blockdiagram.svg)

The block diagram above shows a conceptual view of the `sysrst_ctrl` block, which consists of 3 main modules:
The first is the configuration and status registers, the second is the keyboard combo debounce and detection logic, and the third is the pinout override logic.
The debounce logic does not implement a low-pass filter, instead it uses a simpler technique of sampling once when the timer starts and then again when the timer ends.
The detection logic does require the signal to stay active for the entire period, which can be used to detect any anomoulous signals that might elude the rudimentary debounce logic.
For the auto block, key interrupt and ultra-low-power features there is only a debounce timer so it is good to be aware of this behavior of sampling the signal only twice.

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

## Combo detection

Software can program the `sysrst_ctrl` block to detect certain button combos and for how long they have to be asserted until they trigger a programmable action.
A combo is a combination of multiple keys that are pressed together for a programmable amount of time.

In order to detect a combo, the hardware first OR's the active-low key-pressed indications and debounces the combined trigger signal.
The hardware then detects a negative edge on the combined trigger signal and checks whether it stays asserted low for the programmed amount of cycles.
If the combined trigger signal fulfills the programmed timing constraint, a combo is detected.

Optionally, a combo detection channel may also specify a pre-condition.
Such a pre-condition is a set of keys that must remain pressed in order to activate the combo detection circuit.
The main difference with respect to the combo detection circuit is that the pre-condition checks for a low level of the combined key-pressed indications instead of checking for a negative edge.
The pre-condition debounce timing is the same as for combo detection, but the key-pressed timing can be configured independently.

Let's use the "Power button + Key0 + Key1" combo with pre-condition "Key2" as an example:

0. Software can define the key value `key2_in_i==0` as pre-condition in the [`COM_PRE_SEL_CTL_0`](registers.md#com_pre_sel_ctl) register.
1. The key-pressed time for the pre-condition (e.g. 2 seconds) can be configured via the [`COM_DET_SEL_CTL_0`](registers.md#com_det_sel_ctl) register.
2. Software can define the three key values `pwrb_in_i==0`, `key0_in_i==0` and `key1_in_i==0` as trigger combination in the [`COM_SEL_CTL_0`](registers.md#com_sel_ctl) register.
3. The combo duration for which the above combo should be pressed (e.g. 10 seconds) can be configured via the [`COM_DET_CTL_0`](registers.md#com_det_ctl) register.
4. Actions such as asserting `ec_rst_l_o` and raising an interrupt can be configured via the [`COM_OUT_CTL_0`](registers.md#com_out_ctl) register.
5. The pulse width of the `ec_rst_l_o` pulse can be set in the [`EC_RST_CTL`](registers.md#ec_rst_ctl) register.
6. The software can optionally lock the `sysrst_ctrl` configuration via [`REGWEN`](registers.md#regwen)

Once the above configuration is active, `sysrst_ctrl` will start the timer when the pre-condition is valid (logic 0 level on all pre-condition signals).
If the timing condition (2 seconds) is met, `systrst_ctrl` will enable combo detection, and wait for a high (logic 1) to low (logic 0) transition of the combined trigger signal.
If a transition is seen, and the timing condition is met (10 seconds), `sysrst_ctrl` will assert `ec_rst_l_o`, the interrupt request and set the interrupt status register [`COMBO_INTR_STATUS`](registers.md#combo_intr_status) to indicate the interrupt cause.
The software interrupt handler should then read the [`COMBO_INTR_STATUS`](registers.md#combo_intr_status) register and clear the interrupt via the [`INTR_STATE`](registers.md#intr_state) register.

Note that an interrupt will also issue a wakeup request to the OpenTitan power manager via `wkup_req_o`.
Software should therefore read and clear the [`WKUP_STATUS`](registers.md#wkup_status) register as well.

### Combo actions

The following four combo actions can be triggered:

- Drive the `bat_disable` output high until the next reset.
- Issue an interrupt to the processor via `intr_event_detected_o`.
- Assert `ec_rst_l_o` for the amount of cycles configured in [`EC_RST_CTL`](registers.md#ec_rst_ctl).
- Issue a reset request via `rst_req_o` to the reset manager of the OpenTitan system. Note that once a reset request is issued, it will remain asserted until the next reset.

These actions can be configured via the [`COM_OUT_CTL_0`](registers.md#com_out_ctl) register for each of the combo blocks as described in the previous section.

### Hardwired reset stretching functionality

In addition to the combo action described above, `ec_rst_l_o` is automatically asserted for the amount of cycles defined in the [`EC_RST_CTL`](registers.md#ec_rst_ctl) register whenever the `ec_rst_l_i` input is asserted (i.e., when it transitions from high to low).

## Auto-block key outputs

Software can program the `sysrst_ctrl` block to override the output value of specific passthrough signals, depending on whether certain input signals are asserted or not.
Let's use the "Power button + Esc + Refresh" combo as an example.
When `pwrb_in_i` is asserted, `key1_out_o` (row) should be overridden so that `sysrst_ctrl` can detect if `key0_in_i` (column) is Refresh.

1. The software enables the auto block feature and sets an appropriate debounce timer value in the [`AUTO_BLOCK_DEBOUNCE_CTL`](registers.md#auto_block_debounce_ctl) register.
2. The software then defines the key outputs to auto override and their override values in the [`AUTO_BLOCK_OUT_CTL`](registers.md#auto_block_out_ctl) register.

Once the above configuration is active, `sysrst_ctrl` will detect a high (logic 1) to low (logic 0) transition on `pwrb_in_i` and check whether the key `pwrb_in_i` stays low for the programmed duration.
If this condition is met, `sysrst_ctrl` will drive `key1_out_o` to the value programmed in [`AUTO_BLOCK_OUT_CTL`](registers.md#auto_block_out_ctl).

## Keyboard and input triggered interrupt

Software can program the `sysrst_ctrl` block to detect edge transitions on the `pwrb_in_i`, `key0_in_i`, `key1_in_i`, `key2_in_i`, `ac_present_i`, `ec_rst_l_i` and `flash_wp_l_i` signals and trigger an interrupt:

1. Software first defines the input signal and the edge transition to detect (H->L or L->H) via the [`KEY_INTR_CTL`](registers.md#key_intr_ctl) register.
2. The software then programs an appropriate debounce timer value to the [`KEY_INTR_DEBOUNCE_CTL`](registers.md#key_intr_debounce_ctl) register.

For example, when the power button is pressed, `pwrb_in_i` goes from logic 1 to logic 0 which would amount to an H->L transition.
Likewise, when the power button is released, `pwrb_in_i` goes from logic 0 to logic 1 which would amount to an L->H transition.
When `sysrst_ctrl` detects a transition (H->L or L->H) as specified in [`KEY_INTR_CTL`](registers.md#key_intr_ctl) and it meets the debounce requirement in [`KEY_INTR_DEBOUNCE_CTL`](registers.md#key_intr_debounce_ctl), `sysrst_ctrl` sets the [`KEY_INTR_STATUS`](registers.md#key_intr_status) register to indicate the interrupt cause and send out a consolidated interrupt to the PLIC.
The software interrupt handler should then read the [`KEY_INTR_STATUS`](registers.md#key_intr_status) register and clear the interrupt via the [`INTR_STATE`](registers.md#intr_state) register.

Note that an interrupt will also issue a wakeup request to the OpenTitan power manager via `wkup_req_o`.
Software should therefore read and clear the [`WKUP_STATUS`](registers.md#wkup_status) register as well.

## Ultra-low-power Wakeup Feature

Software can program the `sysrst_ctrl` block to detect certain specific signal transitions on the (possibly inverted) `ac_present_i`, `pwrb_in_i` and `lid_open_i` inputs.
As opposed to the combo detection and general key interrupt features above, this is a fixed function feature with limited configurability.
In particular, the transitions that can be detected are fixed to the following:

- A high level on the `ac_present_i` signal
- A H -> L transition on the `pwrb_in_i` signal
- A L -> H transition on the `lid_open_i` signal

Note that the signals may be potentially inverted due to the [input inversion feature](#pin-output-and-keyboard-inversion-control).

In order to activate this feature, software should do the following:

1. Software can program the appropriate debounce times via the [`ULP_AC_DEBOUNCE_CTL`](registers.md#ulp_ac_debounce_ctl), [`ULP_LID_DEBOUNCE_CTL`](registers.md#ulp_lid_debounce_ctl) and [`ULP_PWRB_DEBOUNCE_CTL`](registers.md#ulp_pwrb_debounce_ctl) registers.
2. Then, software can activate detection by setting the [`ULP_CTL`](registers.md#ulp_ctl) register to 1.

Once the above configuration is active, `sysrst_ctrl` will start the timer when a transition is detected.
Once the timing condition is met, `sysrst_ctrl` will assert `z3_wakeup` output signal, the interrupt request and set the interrupt status register [`ULP_STATUS`](registers.md#ulp_status) to indicate the interrupt cause.
The software interrupt handler should then read the [`ULP_STATUS`](registers.md#ulp_status) register and clear the interrupt via the [`INTR_STATE`](registers.md#intr_state) register.

Note that an interrupt will also issue a wakeup request to the OpenTitan power manager via `wkup_req_o`.
Software should therefore read and clear the [`WKUP_STATUS`](registers.md#wkup_status) register as well.

Also note that the detection status is sticky.
I.e., software needs to explicitly disable this feature by setting [`ULP_CTL`](registers.md#ulp_ctl) to 0 in order to clear the FSM state.
If software wants to re-arm the mechanism right away, it should first read back [`ULP_CTL`](registers.md#ulp_ctl) to make sure it has been cleared before setting that register to 1 again.
This is needed because this register has to be synchronized over to the AON clock domain.

## Pin input value accessibility

`sysrst_ctrl` allows the software to read the raw input pin values via the [`PIN_IN_VALUE`](registers.md#pin_in_value) register like GPIOs.
To this end, the hardware samples the raw input values of `pwrb_in_i`, `key[0,1,2]_in_i`, `ac_present_i`, `ec_rst_l_i`, `flash_wp_l_i` before they are being inverted, and synchronizes them onto the bus clock domain.

## Pin output and keyboard inversion control

Software can optionally override all output signals, and change the signal polarity of some of the input and output signals.
The output signal override feature always has higher priority than any of the combo pattern detection mechanisms described above.

The selection of output signals to override, and the override values are programmable and lockable via the [`PIN_ALLOWED_CTL`](registers.md#pin_allowed_ctl) register.
For example, [`PIN_ALLOWED_CTL.EC_RST_L_0`](registers.md#pin_allowed_ctl) to 1 and [`PIN_ALLOWED_CTL.EC_RST_L_1`](registers.md#pin_allowed_ctl) to 0 means that software allows `ec_rst_l_o` to be overridden with logic 0, but not with logic 1.
If the SW locks the configuration with [`REGWEN`](registers.md#regwen), [`PIN_ALLOWED_CTL`](registers.md#pin_allowed_ctl) cannot be modified until the next OpenTitan reset.

When the system is up and running, the software can modify [`PIN_OUT_CTL`](registers.md#pin_out_ctl) and [`PIN_OUT_VALUE`](registers.md#pin_out_value) to enable or disable the feature.
For example, to release `ec_rst_l_o` after OpenTitan completes the reset, software can set [`PIN_OUT_CTL`](registers.md#pin_out_ctl) to 0 to stop the hardware from driving `ec_rst_l_o` to 0.

The input / output signal inversions can be programmed via the [`KEY_INVERT_CTL`](registers.md#key_invert_ctl) register.
Input signals will be inverted before the combo detection logic, while output signals will be inverted after the output signal override logic.

## EC and Power-on-reset

OpenTitan and EC will be reset together during power-on.
When OpenTitan is in reset, `ec_rst_l_o` will be asserted (active low).
The power-on-reset value of [`PIN_ALLOWED_CTL.EC_RST_L_1`](registers.md#pin_allowed_ctl) and [`PIN_OUT_CTL.EC_RST_L`](registers.md#pin_out_ctl) will guarantee that `ec_rst_l_o` remains asserted after OpenTitan reset is released.
The software can release `ec_rst_l_o` explicitly by setting [`PIN_OUT_CTL.EC_RST_L`](registers.md#pin_out_ctl) to 0 during boot in order to complete the OpenTitan and EC power-on-reset sequence.

Note that since the `sysrst_ctrl` does not have control over the pad open-drain settings, software should properly initialize the pad attributes of the corresponding pad in the [pinmux configuration](../../pinmux/README.md) before releasing `ec_rst_l_o`.

## Flash Write Protect Output

Upon reset, the `flash_wp_l_o` signal will be asserted active low.
The software can release `flash_wp_l_o` explicitly by setting [`PIN_OUT_CTL.FLASH_WP_L`](registers.md#pin_out_ctl) to 0 when needed.
The `flash_wp_l_o` signal does have a corresponding input signal `flash_wp_l_i` - but that one is mainly intended for pad observability and does not have a bypass path to `flash_wp_l_o`.
Hence, the value of `flash_wp_l_o` defaults to logic 0 when it is not explicitly driven via the override function.

Note that since the `sysrst_ctrl` does not have control over the pad open-drain settings, software should properly initialize the pad attributes of the corresponding pad in the [pinmux configuration](../../pinmux/README.md) before releasing `flash_wp_l_o`.

## Device Interface Functions (DIFs)

- [Device Interface Functions](../../../../sw/device/lib/dif/dif_sysrst_ctrl.h)
