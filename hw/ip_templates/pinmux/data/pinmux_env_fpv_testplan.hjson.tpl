// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
<%
top_title = {'earlgrey': 'Earl Grey', 'darjeeling': 'Darjeeling',
             'englishbreakfast': 'English Breakfast'}.get(topname, topname)
eg_top = topname == 'earlgrey'
usb = enable_usb_wakeup
strap = enable_strap_sampling
rram = enable_rram_tap  # the RRAM TAP on TAP strap value 0
# The largest value of each select field, from its width in pinmux.hjson.tpl.
insel_max = 2 ** (n_mio_pads + 1).bit_length() - 1
outsel_max = 2 ** (n_mio_periph_out + 2).bit_length() - 1
outsel_spare = outsel_max > n_mio_periph_out + 2  # a select value names no output
padsel_max = 2 ** max(n_mio_pads + 1, n_dio_pads - 1).bit_length() - 1
def n(base, with_usb=0, with_strap=0, with_rram=0, with_eg=0):
    return (base + (with_usb if usb else 0) + (with_strap if strap else 0)
            + (with_rram if rram else 0) + (with_eg if eg_top else 0))
def free(lo, hi):
    if lo > hi:
        return 'above {} (no such value on this top)'.format(hi)
    return str(lo) if lo == hi else '{} to {}'.format(lo, hi)
def eg(text, other=''):
    return text if eg_top else other
def on(flag, text):
    return text if flag else ''
scan_clk = topname not in 'darjeeling'.split()
lc_top = topname not in 'englishbreakfast'.split()
dm_top = topname not in 'englishbreakfast'.split()
pinmux_aon_only = topname not in 'darjeeling englishbreakfast'.split()
aon_on_sys = topname in 'englishbreakfast'.split()
jtag_dio = topname in 'englishbreakfast'.split()
%>\
{
  name: "pinmux"
  // The planned functional checks of the pinmux FPV environment. A testpoint
  // lists its requirements under `features`; each is defined, with its sources
  // and the reason its checks prove it, in pinmux_fpv_requirements.hjson. A check
  // row may also decide a requirement of another testpoint, which then says so.
  // The register block is checked by the CSR checker in the extended form the
  // plan describes (doc/fpv/README.md); the imported testplan describes the
  // checker as reggen generates it.
  import_testplans: ["hw/dv/tools/dvsim/testplans/fpv_csr_testplan.hjson"]
  testpoints: [
    {
      name: pad_listen
      desc: '''Every peripheral input reads what its select names.

            | Check, and its planned assertion | Kind | Requirements |
            |---|---|---|
            | reads tie 0: `assert_PadListen_ReadsTie0` | forward | [REQ_IN_01](../doc/fpv/requirements.md#req_in_01) |
            | reads tie 1: `assert_PadListen_ReadsTie1` | forward | [REQ_IN_02](../doc/fpv/requirements.md#req_in_02) |
            | reads selected pad: `assert_PadListen_ReadsSelectedPad` | forward | [REQ_IN_03](../doc/fpv/requirements.md#req_in_03) |
            | select without a pad reads 0: `assert_PadListen_SelectWithoutAPadReads0` | legal | [REQ_IN_04](../doc/fpv/requirements.md#req_in_04) |
            | DIO reads its pad: `assert_PadListen_DioReadsItsPad` | forward | [REQ_IN_05](../doc/fpv/requirements.md#req_in_05) |

            5 [requirements](../doc/fpv/requirements.md#input-selection) belong to this testpoint.'''
      stage: V1
      priority: "1"
      tests: ["pinmux_env_fpv"]
      features: ["REQ_IN_01", "REQ_IN_02", "REQ_IN_03", "REQ_IN_04", "REQ_IN_05"]
    }
    {
      name: sparse_insel
      desc: '''An input reads 0 while its select names a pad that its pad list does not allow.

            | Check, and its planned assertion | Kind | Requirements |
            |---|---|---|
            | unlisted pad reads zero: `assert_SparseInsel_UnlistedPadReadsZero` | legal, forward | [REQ_IN_07](../doc/fpv/requirements.md#req_in_07) |

            1 [requirement](../doc/fpv/requirements.md#input-selection) belongs to this testpoint.'''
      stage: V2
      priority: "2"
      tests: ["pinmux_env_fpv"]
      features: ["REQ_IN_07"]
    }
    {
      name: pad_output
      desc: '''Every awake pad drives what its select names.

            | Check, and its planned assertion | Kind | Requirements |
            |---|---|---|
            | tie 0 drives 0: `assert_PadOutput_Tie0Drives0` | forward | [REQ_OUT_01a](../doc/fpv/requirements.md#req_out_01a), [REQ_OUT_01b](../doc/fpv/requirements.md#req_out_01b), [REQ_SLP_08](../doc/fpv/requirements.md#req_slp_08) |
            | tie 1 drives 1: `assert_PadOutput_Tie1Drives1` | forward | [REQ_OUT_02a](../doc/fpv/requirements.md#req_out_02a), [REQ_OUT_02b](../doc/fpv/requirements.md#req_out_02b), [REQ_SLP_08](../doc/fpv/requirements.md#req_slp_08) |
            | select 2 is high-Z: `assert_PadOutput_Select2IsHighZ` | forward | [REQ_OUT_03a](../doc/fpv/requirements.md#req_out_03a), [REQ_OUT_03b](../doc/fpv/requirements.md#req_out_03b), [REQ_SLP_08](../doc/fpv/requirements.md#req_slp_08) |
            | drives selected output: `assert_PadOutput_DrivesSelectedOutput` | forward | [REQ_OUT_04a](../doc/fpv/requirements.md#req_out_04a), [REQ_OUT_04b](../doc/fpv/requirements.md#req_out_04b), [REQ_SLP_08](../doc/fpv/requirements.md#req_slp_08) |
            | select without an output is high-Z: `assert_PadOutput_SelectWithoutAnOutputIsHighZ` | legal | [REQ_OUT_05a](../doc/fpv/requirements.md#req_out_05a), [REQ_OUT_05b](../doc/fpv/requirements.md#req_out_05b), [REQ_SLP_08](../doc/fpv/requirements.md#req_slp_08) |
            | DIO drives its peripheral: `assert_PadOutput_DioDrivesItsPeripheral` | forward | [REQ_OUT_06a](../doc/fpv/requirements.md#req_out_06a), [REQ_OUT_06b](../doc/fpv/requirements.md#req_out_06b), [REQ_SLP_08](../doc/fpv/requirements.md#req_slp_08) |

            12 [requirements](../doc/fpv/requirements.md#output-selection) belong to this testpoint.
            The table also names requirements of other testpoints that its checks help decide.'''
      stage: V1
      priority: "1"
      tests: ["pinmux_env_fpv"]
      features: ["REQ_OUT_01a", "REQ_OUT_01b", "REQ_OUT_02a", "REQ_OUT_02b", "REQ_OUT_03a", "REQ_OUT_03b", "REQ_OUT_04a", "REQ_OUT_04b", "REQ_OUT_05a", "REQ_OUT_05b", "REQ_OUT_06a", "REQ_OUT_06b"]
    }
    {
      name: sparse_outsel
      desc: '''A pad is high-Z while its select names an output whose pad list excludes the pad.

            | Check, and its planned assertion | Kind | Requirements |
            |---|---|---|
            | unlisted output disables pad: `assert_SparseOutsel_UnlistedOutputDisablesPad` | legal, forward | [REQ_OUT_08](../doc/fpv/requirements.md#req_out_08) |
            | disabled pad drives zero: `assert_SparseOutsel_DisabledPadDrivesZero` | legal, forward | [REQ_OUT_08](../doc/fpv/requirements.md#req_out_08) |

            1 [requirement](../doc/fpv/requirements.md#output-selection) belongs to this testpoint.'''
      stage: V2
      priority: "2"
      tests: ["pinmux_env_fpv"]
      features: ["REQ_OUT_08"]
    }
    {
      name: pad_sleep
      desc: '''A pad takes its sleep mode at sleep entry and holds it until software releases the pad.

            | Check, and its planned assertion | Kind | Requirements |
            |---|---|---|
            | bit set at entry: `assert_PadSleep_BitSetAtEntry` | forward | [REQ_SLP_01](../doc/fpv/requirements.md#req_slp_01) |
            | bit set only at entry: `assert_PadSleep_BitSetOnlyAtEntry` | backward | [REQ_SLP_02](../doc/fpv/requirements.md#req_slp_02) |
            | bit holds until cleared: `assert_PadSleep_BitHoldsUntilCleared` | stable | [REQ_SLP_07](../doc/fpv/requirements.md#req_slp_07) |
            | clear releases: `assert_PadSleep_ClearReleases` | forward | [REQ_SLP_07](../doc/fpv/requirements.md#req_slp_07) |
            | clear wins: `assert_PadSleep_ClearWins` | forward | [REQ_SLP_09](../doc/fpv/requirements.md#req_slp_09) |
            | tie low in sleep: `assert_PadSleep_TieLowInSleep` | forward | [REQ_SLP_03a](../doc/fpv/requirements.md#req_slp_03a), [REQ_SLP_03b](../doc/fpv/requirements.md#req_slp_03b), [REQ_SLP_10b](../doc/fpv/requirements.md#req_slp_10b) |
            | tie high in sleep: `assert_PadSleep_TieHighInSleep` | forward | [REQ_SLP_04a](../doc/fpv/requirements.md#req_slp_04a), [REQ_SLP_04b](../doc/fpv/requirements.md#req_slp_04b), [REQ_SLP_10b](../doc/fpv/requirements.md#req_slp_10b) |
            | high-Z in sleep: `assert_PadSleep_HighZInSleep` | forward | [REQ_SLP_05a](../doc/fpv/requirements.md#req_slp_05a), [REQ_SLP_05b](../doc/fpv/requirements.md#req_slp_05b), [REQ_SLP_10b](../doc/fpv/requirements.md#req_slp_10b) |
            | keep holds: `assert_PadSleep_KeepHolds` | stable | [REQ_SLP_06a](../doc/fpv/requirements.md#req_slp_06a), [REQ_SLP_06b](../doc/fpv/requirements.md#req_slp_06b), [REQ_SLP_10b](../doc/fpv/requirements.md#req_slp_10b) |
            | mode write while held: `assert_PadSleep_ModeWriteWhileHeld` | stable | [REQ_SLP_10a](../doc/fpv/requirements.md#req_slp_10a) |

            14 [requirements](../doc/fpv/requirements.md#sleep-retention) belong to this testpoint.'''
      stage: V2
      priority: "2"
      tests: ["pinmux_env_fpv"]
      features: ["REQ_SLP_01", "REQ_SLP_02", "REQ_SLP_03a", "REQ_SLP_03b", "REQ_SLP_04a", "REQ_SLP_04b", "REQ_SLP_05a", "REQ_SLP_05b", "REQ_SLP_06a", "REQ_SLP_06b", "REQ_SLP_07", "REQ_SLP_09", "REQ_SLP_10a", "REQ_SLP_10b"]
    }
    {
      name: pad_attr
      desc: '''A pad receives exactly the attributes that its register reads back.

            | Check, and its planned assertion | Kind | Requirements |
            |---|---|---|
            | pad gets read-back: `assert_PadAttr_PadGetsReadBack` | both | [REQ_ATTR_01a](../doc/fpv/requirements.md#req_attr_01a), [REQ_ATTR_01b](../doc/fpv/requirements.md#req_attr_01b), [REQ_ATTR_01c](../doc/fpv/requirements.md#req_attr_01c), [REQ_ATTR_01d](../doc/fpv/requirements.md#req_attr_01d), [REQ_ATTR_01e](../doc/fpv/requirements.md#req_attr_01e), [REQ_ATTR_01f](../doc/fpv/requirements.md#req_attr_01f), [REQ_ATTR_01g](../doc/fpv/requirements.md#req_attr_01g), [REQ_ATTR_01h](../doc/fpv/requirements.md#req_attr_01h), [REQ_ATTR_01i](../doc/fpv/requirements.md#req_attr_01i), [REQ_ATTR_01j](../doc/fpv/requirements.md#req_attr_01j), [REQ_ATTR_02a](../doc/fpv/requirements.md#req_attr_02a), [REQ_ATTR_02b](../doc/fpv/requirements.md#req_attr_02b), [REQ_ATTR_02c](../doc/fpv/requirements.md#req_attr_02c), [REQ_ATTR_02d](../doc/fpv/requirements.md#req_attr_02d), [REQ_ATTR_02e](../doc/fpv/requirements.md#req_attr_02e), [REQ_ATTR_02f](../doc/fpv/requirements.md#req_attr_02f), [REQ_ATTR_02g](../doc/fpv/requirements.md#req_attr_02g), [REQ_ATTR_02h](../doc/fpv/requirements.md#req_attr_02h), [REQ_ATTR_02i](../doc/fpv/requirements.md#req_attr_02i), [REQ_ATTR_02j](../doc/fpv/requirements.md#req_attr_02j) |
            | invert reads back: `assert_PadAttr_InvertReadsBack` | forward | [REQ_ATTR_03](../doc/fpv/requirements.md#req_attr_03) |
            | virtual open drain reads back: `assert_PadAttr_VirtualOpenDrainReadsBack` | forward | [REQ_ATTR_05](../doc/fpv/requirements.md#req_attr_05) |
            | no open drain: `assert_PadAttr_NoOpenDrain` | legal | [REQ_ATTR_06](../doc/fpv/requirements.md#req_attr_06) |
            | no virtual open drain elsewhere: `assert_PadAttr_NoVirtualOpenDrainElsewhere` | legal | [REQ_ATTR_07](../doc/fpv/requirements.md#req_attr_07) |
            | supported bits read back: `assert_PadAttr_SupportedBitsReadBack` | forward | [REQ_ATTR_08c](../doc/fpv/requirements.md#req_attr_08c), [REQ_ATTR_08d](../doc/fpv/requirements.md#req_attr_08d), [REQ_ATTR_08e](../doc/fpv/requirements.md#req_attr_08e), [REQ_ATTR_08f](../doc/fpv/requirements.md#req_attr_08f), [REQ_ATTR_08g](../doc/fpv/requirements.md#req_attr_08g), [REQ_ATTR_08h](../doc/fpv/requirements.md#req_attr_08h), [REQ_ATTR_08i](../doc/fpv/requirements.md#req_attr_08i) |
            | unsupported bits read 0: `assert_PadAttr_UnsupportedBitsRead0` | legal | [REQ_ATTR_09c](../doc/fpv/requirements.md#req_attr_09c), [REQ_ATTR_09d](../doc/fpv/requirements.md#req_attr_09d), [REQ_ATTR_09e](../doc/fpv/requirements.md#req_attr_09e), [REQ_ATTR_09f](../doc/fpv/requirements.md#req_attr_09f), [REQ_ATTR_09g](../doc/fpv/requirements.md#req_attr_09g), [REQ_ATTR_09h](../doc/fpv/requirements.md#req_attr_09h), [REQ_ATTR_09i](../doc/fpv/requirements.md#req_attr_09i) |
            | reset attributes: `assert_PadAttr_ResetAttributes` | forward | [REQ_ATTR_10](../doc/fpv/requirements.md#req_attr_10) |
            | read-back changes only on a write: `assert_PadAttr_ReadBackChangesOnlyOnAWrite` | stable | [REQ_REG_01a](../doc/fpv/requirements.md#req_reg_01a) |

            39 [requirements](../doc/fpv/requirements.md#pad-attributes) belong to this testpoint.
            The table also names requirements of other testpoints that its checks help decide.'''
      stage: V2
      priority: "2"
      tests: ["pinmux_env_fpv"]
      features: ["REQ_ATTR_01a", "REQ_ATTR_01b", "REQ_ATTR_01c", "REQ_ATTR_01d", "REQ_ATTR_01e", "REQ_ATTR_01f", "REQ_ATTR_01g", "REQ_ATTR_01h", "REQ_ATTR_01i", "REQ_ATTR_01j", "REQ_ATTR_02a", "REQ_ATTR_02b", "REQ_ATTR_02c", "REQ_ATTR_02d", "REQ_ATTR_02e", "REQ_ATTR_02f", "REQ_ATTR_02g", "REQ_ATTR_02h", "REQ_ATTR_02i", "REQ_ATTR_02j", "REQ_ATTR_03", "REQ_ATTR_05", "REQ_ATTR_06", "REQ_ATTR_07", "REQ_ATTR_08c", "REQ_ATTR_08d", "REQ_ATTR_08e", "REQ_ATTR_08f", "REQ_ATTR_08g", "REQ_ATTR_08h", "REQ_ATTR_08i", "REQ_ATTR_09c", "REQ_ATTR_09d", "REQ_ATTR_09e", "REQ_ATTR_09f", "REQ_ATTR_09g", "REQ_ATTR_09h", "REQ_ATTR_09i", "REQ_ATTR_10"]
    }
    {
      name: regwen
      desc: '''A closed attribute lock keeps the attributes of its pad unchanged.

            | Check, and its planned assertion | Kind | Requirements |
            |---|---|---|
            | locked attribute holds: `assert_Regwen_LockedAttributeHolds` | stable | [REQ_LOCK_03a](../doc/fpv/requirements.md#req_lock_03a) |
            | locked read-back holds: `assert_Regwen_LockedReadBackHolds` | stable | [REQ_LOCK_03b](../doc/fpv/requirements.md#req_lock_03b), [REQ_LOCK_02](../doc/fpv/requirements.md#req_lock_02) |

            2 [requirements](../doc/fpv/requirements.md#register-locks) belong to this testpoint.
            The table also names requirements of other testpoints that its checks help decide.'''
      stage: V2
      priority: "2"
      tests: ["pinmux_env_fpv"]
      features: ["REQ_LOCK_03a", "REQ_LOCK_03b"]
    }
    {
      name: bus
      desc: '''Every request receives the answer that the TL-UL rules require, and a failed request changes nothing.

            | Check, and its planned assertion | Kind | Requirements |
            |---|---|---|
            | device rules: `assert_Bus_DeviceRules` | forward | [REQ_BUS_01a](../doc/fpv/requirements.md#req_bus_01a), [REQ_BUS_01b](../doc/fpv/requirements.md#req_bus_01b) |
            | errors as the register checker predicts (through other checks) | both | [REQ_BUS_01c](../doc/fpv/requirements.md#req_bus_01c), [REQ_BUS_10a](../doc/fpv/requirements.md#req_bus_10a), [REQ_BUS_10b](../doc/fpv/requirements.md#req_bus_10b), [REQ_BUS_10c](../doc/fpv/requirements.md#req_bus_10c), [REQ_BUS_10d](../doc/fpv/requirements.md#req_bus_10d), [REQ_BUS_10e](../doc/fpv/requirements.md#req_bus_10e) |
            | response codes correct: `assert_Bus_ResponseCodesCorrect` | forward | [REQ_BUS_02a](../doc/fpv/requirements.md#req_bus_02a), [REQ_BUS_02b](../doc/fpv/requirements.md#req_bus_02b) |
            | failed request errors: `assert_Bus_FailedRequestErrors` | forward | [REQ_BUS_03](../doc/fpv/requirements.md#req_bus_03) |
            | failed write changes nothing: `assert_Bus_FailedWriteChangesNothing` | stable | [REQ_BUS_04](../doc/fpv/requirements.md#req_bus_04) |
            | error write changes nothing (through other checks) | stable | [REQ_BUS_11](../doc/fpv/requirements.md#req_bus_11) |

            13 [requirements](../doc/fpv/requirements.md#register-block-and-bus) belong to this testpoint.'''
      stage: V2
      priority: "2"
      tests: ["pinmux_env_fpv"]
      features: ["REQ_BUS_01a", "REQ_BUS_01b", "REQ_BUS_01c", "REQ_BUS_02a", "REQ_BUS_02b", "REQ_BUS_03", "REQ_BUS_04", "REQ_BUS_10a", "REQ_BUS_10b", "REQ_BUS_10c", "REQ_BUS_10d", "REQ_BUS_10e", "REQ_BUS_11"]
    }
    {
      name: alert
      desc: '''Each ping is answered, and the fatal alert follows only a failed request or an alert test.

            | Check, and its planned assertion | Kind | Requirements |
            |---|---|---|
            | failed request alerts: `assert_Alert_FailedRequestAlerts` | forward | [REQ_BUS_05](../doc/fpv/requirements.md#req_bus_05) |
            | fatal alert repeats: `assert_Alert_FatalAlertRepeats` | forward | [REQ_BUS_06](../doc/fpv/requirements.md#req_bus_06) |
            | test sends an event: `assert_Alert_TestSendsAnEvent` | forward | [REQ_BUS_07](../doc/fpv/requirements.md#req_bus_07) |
            | no alert without a cause: `assert_Alert_NoAlertWithoutACause` | backward | [REQ_BUS_07](../doc/fpv/requirements.md#req_bus_07), [REQ_BUS_08](../doc/fpv/requirements.md#req_bus_08), [REQ_BUS_09](../doc/fpv/requirements.md#req_bus_09), [REQ_BUS_12](../doc/fpv/requirements.md#req_bus_12) |
            | ping answered: `assert_Alert_PingAnswered` | forward | [REQ_BUS_12](../doc/fpv/requirements.md#req_bus_12) |

            6 [requirements](../doc/fpv/requirements.md#register-block-and-bus) belong to this testpoint.'''
      stage: V2S
      priority: "2"
      tests: ["pinmux_env_fpv"]
      features: ["REQ_BUS_05", "REQ_BUS_06", "REQ_BUS_07", "REQ_BUS_08", "REQ_BUS_09", "REQ_BUS_12"]
    }
    {
      name: wakeup
      desc: '''A detector sets its cause bit when it sees its pattern, and at no other time.

            | Check, and its planned assertion | Kind | Requirements |
            |---|---|---|
            | posedge sets cause: `assert_Wakeup_PosedgeSetsCause` | forward | [REQ_WKUP_13a](../doc/fpv/requirements.md#req_wkup_13a), [REQ_WKUP_13b](../doc/fpv/requirements.md#req_wkup_13b), [REQ_WKUP_06a](../doc/fpv/requirements.md#req_wkup_06a), [REQ_WKUP_11](../doc/fpv/requirements.md#req_wkup_11), [REQ_WKUP_14](../doc/fpv/requirements.md#req_wkup_14) |
            | negedge sets cause: `assert_Wakeup_NegedgeSetsCause` | forward | [REQ_WKUP_07a](../doc/fpv/requirements.md#req_wkup_07a), [REQ_WKUP_14](../doc/fpv/requirements.md#req_wkup_14) |
            | edge sets cause: `assert_Wakeup_EdgeSetsCause` | forward | [REQ_WKUP_01](../doc/fpv/requirements.md#req_wkup_01), [REQ_WKUP_02](../doc/fpv/requirements.md#req_wkup_02), [REQ_WKUP_04](../doc/fpv/requirements.md#req_wkup_04), [REQ_WKUP_05](../doc/fpv/requirements.md#req_wkup_05), [REQ_WKUP_08a](../doc/fpv/requirements.md#req_wkup_08a), [REQ_WKUP_14](../doc/fpv/requirements.md#req_wkup_14) |
            | timed high sets cause: `assert_Wakeup_TimedHighSetsCause` | forward | [REQ_WKUP_01](../doc/fpv/requirements.md#req_wkup_01), [REQ_WKUP_09a](../doc/fpv/requirements.md#req_wkup_09a), [REQ_WKUP_14](../doc/fpv/requirements.md#req_wkup_14) |
            | timed low sets cause: `assert_Wakeup_TimedLowSetsCause` | forward | [REQ_WKUP_01](../doc/fpv/requirements.md#req_wkup_01), [REQ_WKUP_03](../doc/fpv/requirements.md#req_wkup_03), [REQ_WKUP_10a](../doc/fpv/requirements.md#req_wkup_10a), [REQ_WKUP_14](../doc/fpv/requirements.md#req_wkup_14) |
            | no false cause: `assert_Wakeup_NoFalseCause` | backward | [REQ_WKUP_01](../doc/fpv/requirements.md#req_wkup_01), [REQ_WKUP_02](../doc/fpv/requirements.md#req_wkup_02), [REQ_WKUP_03](../doc/fpv/requirements.md#req_wkup_03), [REQ_WKUP_04](../doc/fpv/requirements.md#req_wkup_04), [REQ_WKUP_05](../doc/fpv/requirements.md#req_wkup_05), [REQ_WKUP_13a](../doc/fpv/requirements.md#req_wkup_13a), [REQ_WKUP_13b](../doc/fpv/requirements.md#req_wkup_13b), [REQ_WKUP_06b](../doc/fpv/requirements.md#req_wkup_06b), [REQ_WKUP_07b](../doc/fpv/requirements.md#req_wkup_07b), [REQ_WKUP_08b](../doc/fpv/requirements.md#req_wkup_08b), [REQ_WKUP_09b](../doc/fpv/requirements.md#req_wkup_09b), [REQ_WKUP_10b](../doc/fpv/requirements.md#req_wkup_10b), [REQ_WKUP_11](../doc/fpv/requirements.md#req_wkup_11), [REQ_WKUP_12](../doc/fpv/requirements.md#req_wkup_12), [REQ_WKUP_15](../doc/fpv/requirements.md#req_wkup_15) |
            | set lands: `assert_Wakeup_SetLands` | forward | [REQ_WKUP_14](../doc/fpv/requirements.md#req_wkup_14) |
            | cause rises only on a set: `assert_Wakeup_CauseRisesOnlyOnASet` | backward | [REQ_WKUP_15](../doc/fpv/requirements.md#req_wkup_15) |

            21 [requirements](../doc/fpv/requirements.md#wakeup-detectors) belong to this testpoint.'''
      stage: V2
      priority: "1"
      tests: ["pinmux_env_fpv"]
      features: ["REQ_WKUP_01", "REQ_WKUP_02", "REQ_WKUP_03", "REQ_WKUP_04", "REQ_WKUP_05", "REQ_WKUP_13a", "REQ_WKUP_13b", "REQ_WKUP_06a", "REQ_WKUP_06b", "REQ_WKUP_07a", "REQ_WKUP_07b", "REQ_WKUP_08a", "REQ_WKUP_08b", "REQ_WKUP_09a", "REQ_WKUP_09b", "REQ_WKUP_10a", "REQ_WKUP_10b", "REQ_WKUP_11", "REQ_WKUP_12", "REQ_WKUP_14", "REQ_WKUP_15"]
    }
    {
      name: wakeup_cause
      desc: '''A cause bit holds until software clears it, and the wakeup request follows the bits.

            | Check, and its planned assertion | Kind | Requirements |
            |---|---|---|
            | hardware only sets cause: `assert_WakeupCause_HardwareOnlySetsCause` | stable | [REQ_WKUP_16](../doc/fpv/requirements.md#req_wkup_16) |
            | cause holds until cleared: `assert_WakeupCause_CauseHoldsUntilCleared` | stable | [REQ_WKUP_16](../doc/fpv/requirements.md#req_wkup_16) |
            | set and clear together: `assert_WakeupCause_SetAndClearTogether` | forward | [REQ_WKUP_17](../doc/fpv/requirements.md#req_wkup_17) |
            | request follows cause: `assert_WakeupCause_RequestFollowsCause` | forward | [REQ_WKUP_18a](../doc/fpv/requirements.md#req_wkup_18a) |
            | no request without cause: `assert_WakeupCause_NoRequestWithoutCause` | backward | [REQ_WKUP_18b](../doc/fpv/requirements.md#req_wkup_18b) |

            4 [requirements](../doc/fpv/requirements.md#wakeup-detectors) belong to this testpoint.'''
      stage: V2
      priority: "2"
      tests: ["pinmux_env_fpv"]
      features: ["REQ_WKUP_16", "REQ_WKUP_17", "REQ_WKUP_18a", "REQ_WKUP_18b"]
    }
    {
      name: wakeup_sync
      desc: '''Every AON field write and every cause clear reaches the AON logic in a bounded time.

            | Check, and its planned assertion | Kind | Requirements |
            |---|---|---|
            | write lands: `assert_WakeupSync_WriteLands` | forward | [REQ_WKUP_19a](../doc/fpv/requirements.md#req_wkup_19a), [REQ_WKUP_19b](../doc/fpv/requirements.md#req_wkup_19b), [REQ_WKUP_19c](../doc/fpv/requirements.md#req_wkup_19c) |
            | no change without a write: `assert_WakeupSync_NoChangeWithoutAWrite` | backward | [REQ_WKUP_19a](../doc/fpv/requirements.md#req_wkup_19a), [REQ_WKUP_19b](../doc/fpv/requirements.md#req_wkup_19b), [REQ_WKUP_19c](../doc/fpv/requirements.md#req_wkup_19c) |
            | clear lands: `assert_WakeupSync_ClearLands` | forward | [REQ_WKUP_19d](../doc/fpv/requirements.md#req_wkup_19d) |
            | no clear without a write: `assert_WakeupSync_NoClearWithoutAWrite` | backward | [REQ_WKUP_19d](../doc/fpv/requirements.md#req_wkup_19d) |
            | landed clear clears cause: `assert_WakeupSync_LandedClearClearsCause` | forward | [REQ_WKUP_19d](../doc/fpv/requirements.md#req_wkup_19d) |
            | writes land in order: `assert_WakeupSync_WritesLandInOrder` | forward | [REQ_WKUP_20a](../doc/fpv/requirements.md#req_wkup_20a), [REQ_WKUP_20b](../doc/fpv/requirements.md#req_wkup_20b) |

            6 [requirements](../doc/fpv/requirements.md#wakeup-detectors) belong to this testpoint.'''
      stage: V2
      priority: "2"
      tests: ["pinmux_env_fpv"]
      features: ["REQ_WKUP_19a", "REQ_WKUP_19b", "REQ_WKUP_19c", "REQ_WKUP_19d", "REQ_WKUP_20a", "REQ_WKUP_20b"]
    }
% if usb:
    {
      name: usb_conn
      desc: '''Every port of the USB wakeup module carries the pinmux signal of the same role.

            | Check, and its planned assertion | Kind | Requirements |
            |---|---|---|
            | D+ pull-up enable in: `assert_UsbConn_DpPullUpEnableIn` | both | [REQ_USB_01a](../doc/fpv/requirements.md#req_usb_01a) |
            | D- pull-up enable in: `assert_UsbConn_DnPullUpEnableIn` | both | [REQ_USB_01b](../doc/fpv/requirements.md#req_usb_01b) |
            | suspend request in: `assert_UsbConn_SuspendRequestIn` | both | [REQ_USB_01c](../doc/fpv/requirements.md#req_usb_01c) |
            | wake acknowledge in: `assert_UsbConn_WakeAcknowledgeIn` | both | [REQ_USB_01d](../doc/fpv/requirements.md#req_usb_01d) |
            | D+ pull-up enable out: `assert_UsbConn_DpPullUpEnableOut` | both | [REQ_USB_02a](../doc/fpv/requirements.md#req_usb_02a) |
            | D- pull-up enable out: `assert_UsbConn_DnPullUpEnableOut` | both | [REQ_USB_02b](../doc/fpv/requirements.md#req_usb_02b) |
            | bus not idle out: `assert_UsbConn_BusNotIdleOut` | both | [REQ_USB_02c](../doc/fpv/requirements.md#req_usb_02c) |
            | bus reset out: `assert_UsbConn_BusResetOut` | both | [REQ_USB_02d](../doc/fpv/requirements.md#req_usb_02d) |
            | sense lost out: `assert_UsbConn_SenseLostOut` | both | [REQ_USB_02e](../doc/fpv/requirements.md#req_usb_02e) |
            | active out: `assert_UsbConn_ActiveOut` | both | [REQ_USB_02f](../doc/fpv/requirements.md#req_usb_02f) |
            | wake request out: `assert_UsbConn_WakeRequestOut` | both | [REQ_USB_03](../doc/fpv/requirements.md#req_usb_03) |
            | module on AON clock: `assert_UsbConn_ModuleOnAonClock` | both | [REQ_USB_04a](../doc/fpv/requirements.md#req_usb_04a) |
            | module on AON reset: `check_UsbConn_ModuleOnAonReset` | structure | [REQ_USB_04b](../doc/fpv/requirements.md#req_usb_04b) |
            | bus inputs: `assert_UsbConn_BusInputs` | both | [REQ_USB_05a](../doc/fpv/requirements.md#req_usb_05a), [REQ_USB_05b](../doc/fpv/requirements.md#req_usb_05b), [REQ_USB_05c](../doc/fpv/requirements.md#req_usb_05c) |

            16 [requirements](../doc/fpv/requirements.md#usb-wakeup) belong to this testpoint.'''
      stage: V2
      priority: "2"
      tests: ["pinmux_env_fpv"]
      features: ["REQ_USB_01a", "REQ_USB_01b", "REQ_USB_01c", "REQ_USB_01d", "REQ_USB_02a", "REQ_USB_02b", "REQ_USB_02c", "REQ_USB_02d", "REQ_USB_02e", "REQ_USB_02f", "REQ_USB_03", "REQ_USB_04a", "REQ_USB_04b", "REQ_USB_05a", "REQ_USB_05b", "REQ_USB_05c"]
    }
% endif
% if usb:
    {
      name: usb_module
      desc: '''The USB wakeup module takes over the pull-ups, stores its events and requests the wakeup.

            | Check, and its planned assertion | Kind | Requirements |
            |---|---|---|
            | request activates: `assert_UsbModule_RequestActivates` | forward | [REQ_USB_06a](../doc/fpv/requirements.md#req_usb_06a) |
            | acknowledge releases: `assert_UsbModule_AcknowledgeReleases` | forward | [REQ_USB_06b](../doc/fpv/requirements.md#req_usb_06b) |
            | no other state change: `assert_UsbModule_NoOtherStateChange` | backward | [REQ_USB_06c](../doc/fpv/requirements.md#req_usb_06c) |
            | inactive passes pull-ups: `assert_UsbModule_InactivePassesPullUps` | both | [REQ_USB_06d](../doc/fpv/requirements.md#req_usb_06d) |
            | active holds pull-ups: `assert_UsbModule_ActiveHoldsPullUps` | stable | [REQ_USB_06e](../doc/fpv/requirements.md#req_usb_06e) |
            | pull-ups after VBUS loss: `assert_UsbModule_PullUpsAfterVbusLoss` | waits on a specification question | [REQ_USB_06e](../doc/fpv/requirements.md#req_usb_06e) |
            | held condition sets event: `assert_UsbModule_HeldConditionSetsEvent` | forward | [REQ_USB_06f](../doc/fpv/requirements.md#req_usb_06f) |
            | event only after its condition: `assert_UsbModule_EventOnlyAfterItsCondition` | backward | [REQ_USB_06g](../doc/fpv/requirements.md#req_usb_06g) |
            | short condition sets no event: `assert_UsbModule_ShortConditionSetsNoEvent` | waits on a specification question | [REQ_USB_06g](../doc/fpv/requirements.md#req_usb_06g) |
            | event holds while active: `assert_UsbModule_EventHoldsWhileActive` | stable | [REQ_USB_06h](../doc/fpv/requirements.md#req_usb_06h) |
            | acknowledge clears events: `assert_UsbModule_AcknowledgeClearsEvents` | forward | [REQ_USB_06i](../doc/fpv/requirements.md#req_usb_06i) |
            | wake request follows events: `assert_UsbModule_WakeRequestFollowsEvents` | both | [REQ_USB_06j](../doc/fpv/requirements.md#req_usb_06j) |

            10 [requirements](../doc/fpv/requirements.md#usb-wakeup) belong to this testpoint.'''
      stage: V2
      priority: "2"
      tests: ["pinmux_env_fpv"]
      features: ["REQ_USB_06a", "REQ_USB_06b", "REQ_USB_06c", "REQ_USB_06d", "REQ_USB_06e", "REQ_USB_06f", "REQ_USB_06g", "REQ_USB_06h", "REQ_USB_06i", "REQ_USB_06j"]
    }
% endif
% if strap:
    {
      name: strap
      desc: '''The TAP straps sample their pads as the life cycle allows and hold their values otherwise.

            | Check, and its planned assertion | Kind | Requirements |
            |---|---|---|
            | pulse samples the straps: `assert_Strap_PulseSamplesTheStraps` | forward | [REQ_STRAP_01](../doc/fpv/requirements.md#req_strap_01), [REQ_STRAP_02a](../doc/fpv/requirements.md#req_strap_02a), [REQ_STRAP_02b](../doc/fpv/requirements.md#req_strap_02b), [REQ_STRAP_06](../doc/fpv/requirements.md#req_strap_06), [REQ_TAP_05](../doc/fpv/requirements.md#req_tap_05) |
            | straps follow the pads: `assert_Strap_StrapsFollowThePads` | forward | [REQ_STRAP_03](../doc/fpv/requirements.md#req_strap_03) |
            | straps hold: `assert_Strap_StrapsHold` | stable | [REQ_STRAP_04](../doc/fpv/requirements.md#req_strap_04), [REQ_STRAP_05](../doc/fpv/requirements.md#req_strap_05), [REQ_STRAP_06](../doc/fpv/requirements.md#req_strap_06), [REQ_STRAP_08](../doc/fpv/requirements.md#req_strap_08), [REQ_TAP_05](../doc/fpv/requirements.md#req_tap_05) |
            | unsampled strap reads 0: `assert_Strap_UnsampledStrapReads0` | forward | [REQ_STRAP_06](../doc/fpv/requirements.md#req_strap_06) |
            | straps outside NDM reset: `check_Strap_StrapsOutsideNdmReset` | structure | [REQ_STRAP_07](../doc/fpv/requirements.md#req_strap_07) |

            9 [requirements](../doc/fpv/requirements.md#strap-sampling) belong to this testpoint.
            The table also names requirements of other testpoints that its checks help decide.'''
      stage: V2S
      priority: "1"
      tests: ["pinmux_env_fpv"]
      features: ["REQ_STRAP_01", "REQ_STRAP_02a", "REQ_STRAP_02b", "REQ_STRAP_03", "REQ_STRAP_04", "REQ_STRAP_05", "REQ_STRAP_06", "REQ_STRAP_07", "REQ_STRAP_08"]
    }
% endif
% if strap:
    {
      name: dft_strap
      desc: '''The DFT straps are sampled once at boot in the test states and held.

            | Check, and its planned assertion | Kind | Requirements |
            |---|---|---|
            | pulse samples DFT straps: `assert_DftStrap_PulseSamplesDftStraps` | forward | [REQ_DFT_01a](../doc/fpv/requirements.md#req_dft_01a), [REQ_DFT_01b](../doc/fpv/requirements.md#req_dft_01b) |
            | DFT straps held: `assert_DftStrap_DftStrapsHeld` | stable | [REQ_DFT_02a](../doc/fpv/requirements.md#req_dft_02a), [REQ_DFT_02b](../doc/fpv/requirements.md#req_dft_02b) |
            | zero until sampled: `assert_DftStrap_ZeroUntilSampled` | backward | [REQ_DFT_03](../doc/fpv/requirements.md#req_dft_03) |

            5 [requirements](../doc/fpv/requirements.md#dft-straps) belong to this testpoint.'''
      stage: V2S
      priority: "2"
      tests: ["pinmux_env_fpv"]
      features: ["REQ_DFT_01a", "REQ_DFT_01b", "REQ_DFT_02a", "REQ_DFT_02b", "REQ_DFT_03"]
    }
% endif
% if strap:
    {
      name: latch
      desc: '''The latch takes the debug enable at boot, turns Off at a life cycle clear, and holds otherwise.

            | Check, and its planned assertion | Kind | Requirements |
            |---|---|---|
            | Off from full reset: `assert_Latch_OffFromFullReset` | forward | [REQ_DBG_08](../doc/fpv/requirements.md#req_dbg_08) |
            | pulse samples debug enable: `assert_Latch_PulseSamplesDebugEnable` | forward | [REQ_DBG_01a](../doc/fpv/requirements.md#req_dbg_01a), [REQ_DBG_01b](../doc/fpv/requirements.md#req_dbg_01b), [REQ_DBG_06](../doc/fpv/requirements.md#req_dbg_06), [REQ_DBG_07a](../doc/fpv/requirements.md#req_dbg_07a), [REQ_TAP_05](../doc/fpv/requirements.md#req_tap_05) |
            | On only at a pulse: `assert_Latch_OnOnlyAtAPulse` | backward | [REQ_DBG_01b](../doc/fpv/requirements.md#req_dbg_01b), [REQ_DBG_07b](../doc/fpv/requirements.md#req_dbg_07b), [REQ_DBG_08](../doc/fpv/requirements.md#req_dbg_08) |
            | clear turns Off: `assert_Latch_ClearTurnsOff` | forward | [REQ_DBG_03](../doc/fpv/requirements.md#req_dbg_03), [REQ_DBG_04](../doc/fpv/requirements.md#req_dbg_04), [REQ_DBG_05](../doc/fpv/requirements.md#req_dbg_05), [REQ_DBG_07b](../doc/fpv/requirements.md#req_dbg_07b), [REQ_DBG_09](../doc/fpv/requirements.md#req_dbg_09) |
            | latch holds: `assert_Latch_LatchHolds` | stable | [REQ_DBG_02](../doc/fpv/requirements.md#req_dbg_02), [REQ_DBG_06](../doc/fpv/requirements.md#req_dbg_06), [REQ_DBG_07a](../doc/fpv/requirements.md#req_dbg_07a) |
            | output On or Off: `assert_Latch_OutputOnOrOff` | legal | [REQ_DBG_07a](../doc/fpv/requirements.md#req_dbg_07a), [REQ_DBG_07b](../doc/fpv/requirements.md#req_dbg_07b) |
            | latch outside NDM reset: `check_Latch_LatchOutsideNdmReset` | structure | [REQ_DBG_02](../doc/fpv/requirements.md#req_dbg_02) |

            11 [requirements](../doc/fpv/requirements.md#latched-debug-enable) belong to this testpoint.
            The table also names requirements of other testpoints that its checks help decide.'''
      stage: V2S
      priority: "1"
      tests: ["pinmux_env_fpv"]
      features: ["REQ_DBG_01a", "REQ_DBG_01b", "REQ_DBG_02", "REQ_DBG_03", "REQ_DBG_04", "REQ_DBG_05", "REQ_DBG_06", "REQ_DBG_07a", "REQ_DBG_07b", "REQ_DBG_08", "REQ_DBG_09"]
    }
% endif
% if strap:
    {
      name: jtag
      desc: '''The TAP that the straps name is connected to the JTAG pads only while life cycle allows it.

            | Check, and its planned assertion | Kind | Requirements |
            |---|---|---|
            | connected TAP gets the pads: `assert_Jtag_ConnectedTapGetsThePads` | forward | [REQ_TAP_01a](../doc/fpv/requirements.md#req_tap_01a), [REQ_TAP_01b](../doc/fpv/requirements.md#req_tap_01b), [REQ_TAP_01c](../doc/fpv/requirements.md#req_tap_01c), [REQ_TAP_01d](../doc/fpv/requirements.md#req_tap_01d), [REQ_TAP_02a](../doc/fpv/requirements.md#req_tap_02a), [REQ_TAP_03a](../doc/fpv/requirements.md#req_tap_03a), [REQ_TAP_12](../doc/fpv/requirements.md#req_tap_12)${on(rram, ', [REQ_RRAM_06](../doc/fpv/requirements.md#req_rram_06)')} |
            | cut TAP gets zero: `assert_Jtag_CutTapGetsZero` | backward | [REQ_TAP_02b](../doc/fpv/requirements.md#req_tap_02b), [REQ_TAP_03b](../doc/fpv/requirements.md#req_tap_03b), [REQ_TAP_04](../doc/fpv/requirements.md#req_tap_04), [REQ_TAP_05](../doc/fpv/requirements.md#req_tap_05), [REQ_TAP_12](../doc/fpv/requirements.md#req_tap_12)${on(rram, ', [REQ_RRAM_06](../doc/fpv/requirements.md#req_rram_06)')} |
            | only On opens (through other checks) | legal | [REQ_TAP_05](../doc/fpv/requirements.md#req_tap_05) |
            | TAP selection outside NDM reset: `check_Jtag_TapSelectionOutsideNdmReset` | structure | [REQ_TAP_12](../doc/fpv/requirements.md#req_tap_12) |

            11 [requirements](../doc/fpv/requirements.md#tap-selection-and-the-jtag-pads) belong to this testpoint.
            The table also names requirements of other testpoints that its checks help decide.'''
      stage: V2S
      priority: "1"
      tests: ["pinmux_env_fpv"]
      features: ["REQ_TAP_01a", "REQ_TAP_01b", "REQ_TAP_01c", "REQ_TAP_01d", "REQ_TAP_02a", "REQ_TAP_02b", "REQ_TAP_03a", "REQ_TAP_03b", "REQ_TAP_04", "REQ_TAP_05", "REQ_TAP_12"]
    }
% endif
% if rram:
    {
      name: rram_tap
      desc: '''The RRAM TAP is connected to the JTAG pads on TAP straps 00 only while its register and life cycle allow it.

            | Check, and its planned assertion | Kind | Requirements |
            |---|---|---|
            | connected RRAM TAP gets the pads: `assert_RramTap_ConnectedRramTapGetsThePads` | forward | [REQ_RRAM_01](../doc/fpv/requirements.md#req_rram_01) |
            | cut RRAM TAP gets TMS and TDI 0: `assert_RramTap_CutRramTapGetsTmsAndTdi0` | backward | [REQ_RRAM_02](../doc/fpv/requirements.md#req_rram_02), [REQ_RRAM_04](../doc/fpv/requirements.md#req_rram_04), [REQ_RRAM_07](../doc/fpv/requirements.md#req_rram_07) |
            | only True and On open (through other checks) | legal | [REQ_RRAM_04](../doc/fpv/requirements.md#req_rram_04) |
            | TCK and TRST low after a cut: `assert_RramTap_TckAndTrstLowAfterACut` | backward | [REQ_RRAM_03](../doc/fpv/requirements.md#req_rram_03) |
            | RRAM TAP kept through a transition: `assert_RramTap_RramTapKeptThroughATransition` | stable | [REQ_RRAM_07](../doc/fpv/requirements.md#req_rram_07) |
            | cut until the register is written: `assert_RramTap_CutUntilTheRegisterIsWritten` | backward | [REQ_RRAM_05](../doc/fpv/requirements.md#req_rram_05) |
            | TCK and TRST run one cycle more: `assert_RramTap_TckAndTrstRunOneCycleMore` | forward | [REQ_RRAM_09](../doc/fpv/requirements.md#req_rram_09) |

            8 [requirements](../doc/fpv/requirements.md#rram-tap) belong to this testpoint.'''
      stage: V2S
      priority: "2"
      tests: ["pinmux_env_fpv"]
      features: ["REQ_RRAM_01", "REQ_RRAM_02", "REQ_RRAM_03", "REQ_RRAM_09", "REQ_RRAM_04", "REQ_RRAM_05", "REQ_RRAM_06", "REQ_RRAM_07"]
    }
% endif
% if strap:
    {
      name: jtag_pad
      desc: '''While a TAP is connected, the five JTAG pads belong to it.

            | Check, and its planned assertion | Kind | Requirements |
            |---|---|---|
            | TDO pad drives the TAP: `assert_JtagPad_TdoPadDrivesTheTap` | forward | [REQ_TAP_06a](../doc/fpv/requirements.md#req_tap_06a), [REQ_TAP_06b](../doc/fpv/requirements.md#req_tap_06b) |
            | input pads not driven: `assert_JtagPad_InputPadsNotDriven` | forward | [REQ_TAP_07](../doc/fpv/requirements.md#req_tap_07) |
            | JTAG attributes zero: `assert_JtagPad_JtagAttributesZero` | forward | [REQ_TAP_08](../doc/fpv/requirements.md#req_tap_08) |
            | attribute registers untouched: `assert_JtagPad_AttributeRegistersUntouched` | stable | [REQ_TAP_09](../doc/fpv/requirements.md#req_tap_09) |

            5 [requirements](../doc/fpv/requirements.md#tap-selection-and-the-jtag-pads) belong to this testpoint.'''
      stage: V2S
      priority: "2"
      tests: ["pinmux_env_fpv"]
      features: ["REQ_TAP_06a", "REQ_TAP_06b", "REQ_TAP_07", "REQ_TAP_08", "REQ_TAP_09"]
    }
% endif
    {
      name: reset_state
      desc: '''An input reads its default and an awake pad drives its default until its select is written.

            | Check, and its planned assertion | Kind | Requirements |
            |---|---|---|
            | input starts at default: `assert_ResetState_InputStartsAtDefault` | forward | [REQ_IN_06](../doc/fpv/requirements.md#req_in_06) |
            | pad starts at default: `assert_ResetState_PadStartsAtDefault` | forward | [REQ_OUT_07](../doc/fpv/requirements.md#req_out_07) |

            2 [requirements](../doc/fpv/requirements.md#input-selection) belong to this testpoint.'''
      stage: V2
      priority: "2"
      tests: ["pinmux_env_fpv"]
      features: ["REQ_IN_06", "REQ_OUT_07"]
    }
    {
      name: sleep_release
      desc: '''A pad whose status bit is 0 drives what its select names.

            This testpoint has no check of its own. The checks of other testpoints decide its requirements.

            | Requirement | Decided by |
            |---|---|
            | [REQ_SLP_08](../doc/fpv/requirements.md#req_slp_08) | `pad_output`: *tie 0 drives 0*, *tie 1 drives 1*, *select 2 is high-Z*, *drives selected output*, *select without an output is high-Z*, *DIO drives its peripheral* |'''
      stage: V2
      priority: "2"
      tests: ["pinmux_env_fpv"]
      features: ["REQ_SLP_08"]
    }
    {
      name: register_block
      desc: '''The CSR checker checks every field against its access type, reset value and lock.

            This testpoint has no assertion in the feature checkers.
            The CSR checker decides its requirements, in the extended form that the plan page describes in its section CSR checker.
            The imported testpoint `fpv_csr_rw` describes the checker as reggen generates it, without the extension.

            | Requirement | Decided by |
            |---|---|
            | [REQ_REG_01a](../doc/fpv/requirements.md#req_reg_01a) | `pad_attr`: *read-back changes only on a write*; the CSR checker |
            | [REQ_REG_01b](../doc/fpv/requirements.md#req_reg_01b) | the CSR checker |
            | [REQ_LOCK_01a](../doc/fpv/requirements.md#req_lock_01a) | the CSR checker |
            | [REQ_LOCK_01b](../doc/fpv/requirements.md#req_lock_01b) | the CSR checker |
            | [REQ_LOCK_01c](../doc/fpv/requirements.md#req_lock_01c) | the CSR checker |
            | [REQ_LOCK_02](../doc/fpv/requirements.md#req_lock_02) | `regwen`: *locked read-back holds*; the CSR checker |'''
      stage: V2
      priority: "2"
      tests: ["pinmux_env_fpv"]
      features: ["REQ_REG_01a", "REQ_REG_01b", "REQ_LOCK_01a", "REQ_LOCK_01b", "REQ_LOCK_01c", "REQ_LOCK_02"]
    }
  ]
}
