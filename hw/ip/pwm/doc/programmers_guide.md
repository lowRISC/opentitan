# Programmer's Guide

To set the PWM Frequency for the entire IP:
1. Clear [`CFG.CNTR_EN`](../data/pwm.hjson#cfg)
2. Select [`CFG.CLK_DIV`](../data/pwm.hjson#cfg)
3. Assert [`CFG.CNTR_EN`](../data/pwm.hjson#cfg)

To configure the fixed PWM duty cycle and for a particular output channel (for example channel 0):

1. Disable blinking by clearing the [`PWM_PARAM_0.BLINK_EN_0`](../data/pwm.hjson#pwm_param_0) bit.
2. Set [`DUTY_CYCLE_0.A_0`](../data/pwm.hjson#duty_cycle_0)
3. Optionally set [`PWM_PARAM_0.PHASE_DELAY_0`](../data/pwm.hjson#pwm_param_0) to adjust the pulse phase.
4. Optionally assert [`INVERT.INVERT_0`](../data/pwm.hjson#invert) to flip the polarity.
5. Set [`PWM_EN.EN_0`](../data/pwm.hjson#pwm_en) to turn the channel on.

These changes will take place immediately, regardless of whether the `phase_ctr` is currently in the middle of a pulse cycle.

To activate simple blinking for channel 0:

1. Set [`DUTY_CYCLE_0.A_0`](../data/pwm.hjson#duty_cycle_0) and [`DUTY_CYCLE_0.B_0`](../data/pwm.hjson#duty_cycle_0) to establish the initial and target duty cycles.
2. Clear the [`PWM_PARAM_0.BLINK_EN_0`](../data/pwm.hjson#pwm_param_0) and [`PWM_PARAM_0.HTBT_EN_0`](../data/pwm.hjson#pwm_param_0) bits.
This step is necessary for changing the blink timing parameters
3. Set  [`BLINK_PARAM_0.X_0`](../data/pwm.hjson#blink_param_0) and [`BLINK_PARAM_0.Y_0`](../data/pwm.hjson#blink_param_0) to set the number of pulse cycles respectively spent at duty cycle A and duty cycle B.
4. Re-assert [`PWM_PARAM_0.BLINK_EN_0`](../data/pwm.hjson#pwm_param_0).

For synchronous blinking of a group of channels, first disable the desired channels using the [`PWM_EN`](../data/pwm.hjson#pwm_en) register.
Then after configuring the blink properties of the entire group, re-enable them with a single write to [`PWM_EN`](../data/pwm.hjson#pwm_en).

To activate heartbeat blinking for channel 0:
1. Set [`DUTY_CYCLE_0.A_0`](../data/pwm.hjson#duty_cycle_0) and [`DUTY_CYCLE_0.B_0`](../data/pwm.hjson#duty_cycle_0) to establish the initial and target duty cycles.
2. Clear the [`PWM_PARAM_0.BLINK_EN_0`](../data/pwm.hjson#pwm_param_0) bit.
This step is necessary for changing the blink timing parameters
3. Set [`BLINK_PARAM_0.X_0`](../data/pwm.hjson#blink_param_0) to the number of pulse cycles between duty cycle steps (i.e. increments or decrements).
4. Set [`BLINK_PARAM_0.Y_0`](../data/pwm.hjson#blink_param_0) to set the size of each step.
5. In a single write, assert both [`PWM_PARAM_0.BLINK_EN_0`](../data/pwm.hjson#pwm_param_0) and [`PWM_PARAM_0.HTBT_EN_0`](../data/pwm.hjson#pwm_param_0)

## Device Interface Functions (DIFs)

- [Device Interface Functions](../../../../sw/ip/pwm/dif/dif_pwm.h)

## Register Table

* [Register Table](../data/pwm.hjson#registers)
