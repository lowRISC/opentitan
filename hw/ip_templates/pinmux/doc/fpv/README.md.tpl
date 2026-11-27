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
# Pinmux FPV testplan

This page is the plan of a new pinmux FPV environment for ${top_title}.
The environment proves the pinmux requirements for every pad, select value and register setting.
[Scope](#scope) lists what it checks and what it leaves out.
Every assertion traces to a requirement, and every requirement names its source.
The existing pinmux FPV testbench and its testplan stay as they are ([DV document](../dv/README.md)), and this environment is added beside them.

${"##"} The pinmux in ${top_title}
The pinmux connects the chip's peripherals to its pads.
A muxed pad (MIO) carries the peripheral signal that software selects for it.
A dedicated pad (DIO) is wired to one peripheral signal.
Software writes the pinmux registers over TL-UL to choose the connections and to set each pad's attributes, such as a pull-up or an inversion.
The top's configuration can limit each peripheral signal to a list of pads.
It also sets the reset value of each select and of each pad's attributes.
The pinmux also does these jobs with its neighbours:

* With the power manager, it holds the pad values during sleep (sleep retention).
  It also wakes the chip when a wakeup detector sees its pattern on a pad.
% if strap:
* ${'With the life cycle controller, it' if lc_top else 'It'} decides which JTAG test access port (TAP) is connected to the JTAG pads.
  The straps are the pads that choose the TAP.
  The pinmux samples them at boot or in every cycle, as the life cycle state requires, and it connects the chosen TAP only while ${'the life cycle controller allows' if lc_top else 'its life cycle inputs allow'} it.
  For the RISC-V TAP, which is the debug TAP, the pinmux takes the permission at boot and holds it.
  This held value is the latched debug enable.
% endif
% if strap and not lc_top and not dm_top:
  This top has no life cycle controller and no `rv_dm`.
  The plan still checks the pinmux ports that face them, with their inputs free.
% endif
% if usb:
* For usbdev, it holds the USB wakeup module${on(pinmux_aon_only, ', because the pinmux stays powered in sleep and usbdev does not')}.
% endif
* To the alert handler, it reports a fatal bus fault.

![The pinmux and its neighbours, drawn for Earl Grey: the signals it exchanges with each, and the FPV boundary at its ports](pinmux_fpv_system.svg)

The environment sits at the pinmux's own ports.
It drives every input and checks every output, and no neighbour is part of a proof.
The table lists the ports of each neighbour and what the environment does with them.
It also lists the clocks and resets, which the figure leaves out.
An input marked free can take any value in any cycle.

| Neighbour | Ports: pinmux inputs; outputs${on(strap, ' and TAP ports')} | In the environment |
|---|---|---|
| Peripherals | `periph_to_mio_i`, `periph_to_mio_oe_i`, `periph_to_dio_i`, `periph_to_dio_oe_i`; `mio_to_periph_o`, `dio_to_periph_o` | Peripheral outputs free; the inputs the peripherals read checked |
| Pad ring | `mio_in_i`, `dio_in_i`; `mio_out_o`, `mio_oe_o`, `mio_attr_o`, `dio_out_o`, `dio_oe_o`, `dio_attr_o` | Pad inputs free; pad outputs and attributes checked |
| TL-UL host | `tl_i`; `tl_o` | The host's handshake assumed; its requests free, legal and illegal; the responses checked |
| Alert handler | `alert_rx_i`; `alert_tx_o` | Handler rules assumed; the fatal alert and the ping answers checked |
| Power manager | `sleep_en_i`${on(strap, ', `strap_en_i`')}; `pin_wkup_req_o`${on(usb, ', `usb_wkup_req_o`')} | Sleep input${on(strap, ' and strap pulse')} assumed; wakeup requests checked |
% if strap:
| Life cycle controller${on(not lc_top, ' (not on this top)')} | `lc_dft_en_i`, `lc_hw_debug_en_i`, `lc_hw_debug_clr_i`, `lc_escalate_en_i`, `lc_check_byp_en_i`${on(rram, ', `lc_nvm_debug_en_i`')}, `strap_en_override_i`; `lc_jtag` | The life cycle signals free, any 4-bit value; `strap_en_override_i` free; the TAP port checked |
| `rv_dm`${on(not dm_top, ' (not on this top)')} | `rv_jtag`; `pinmux_hw_debug_en_o` | TAP responses free; TAP requests and the latched debug enable checked |
% endif
| DFT and AST | `scanmode_i`${on(strap, ', `dft_hold_tap_sel_i`; `dft_jtag`, `dft_strap_test_o`')} | Scan mode free${on(scan_clk, ', held off in a few checks only ([Constraints](#constraints))')}${on(strap, '; the DFT TAP port and the sampled DFT straps checked')} |
% if rram:
| RRAM macro | `rram_jtag` | TAP responses free; TAP requests checked |
% endif
% if usb:
| usbdev and the USB PHY | the `usbdev_*` ports; `usb_dppullup_en_o`, `usb_dnpullup_en_o` | usbdev's signals and the USB lines free, with one assumption on the pull-up enables ([Assumptions](#assumptions)); the USB wakeup module's wiring and behaviour checked |
% endif
| Clock and reset managers | `clk_i`, `clk_aon_i`, `rst_ni`, `rst_aon_ni`${on(strap, ', `rst_sys_ni`')} | Fixed clock ratio and one reset at the start ([Constraints](#constraints)) |

${"##"} How the plan fits together
The plan is a chain of four parts.
Each part points to the next, so a specification section leads to the assertions that check it, and a failing assertion leads back to the specification text.

1. **Specification.**
   The documents that say what the pinmux must do: [Sources](#sources) lists them.
2. **Requirements** ([requirements.md](requirements.md)).
   ${n(133, 26, 41, 8)} statements of what the pinmux must do, one group per feature.
   Each requirement names its source.
3. **Testpoints** ([testplan](../../data/pinmux_env_fpv_testplan.hjson)).
   ${n(15, 2, 5, 1)} entries of the testplan.
   The testplan also imports the one testpoint of reggen's CSR checker, `fpv_csr_rw`, so its page shows one more.
   A testpoint is one behaviour of a feature that must be shown to hold, written as one sentence, with the requirements it covers.
   A testpoint is not a module of the testbench.
   The module that proves it is a checker, and one checker proves one or more testpoints ([Feature checkers](#feature-checkers)).
4. **Checks.**
   ${n(67, 26, 23, 7)} checks, the rows of the testpoints' check tables.
   A check is a sentence that says what must hold.
   ${n(65, 23, 19, 6)} of them are decided by a planned assertion of their own, named `assert_<Testpoint>_<Check>`.
   [Check kinds](#check-kinds) says what the other checks are.
   A testpoint lists its checks.
   A requirement names what decides it, and why: its checks or the CSR checker.

Two more words describe the testbench.
A checker is a module that holds the assertions of one feature, or of a few related ones ([Feature checkers](#feature-checkers)).
A proof is one run of the formal tool on the assertions of one checker, or of a part of them ([Proofs](#proofs)).

${"###"} One example through the chain
| Step | Example |
|---|---|
| Specification | [`MIO_PERIPH_INSEL.IN`](../registers.md#mio_periph_insel); [Muxing Matrix](../theory_of_operation.md#muxing-matrix); [top_${topname}_pinmux.ipconfig.hjson `n_mio_pads`](../../data/top_${topname}_pinmux.ipconfig.hjson); [top_${topname}_pinmux.ipconfig.hjson `mio_periph_ins`](../../data/top_${topname}_pinmux.ipconfig.hjson) |
| Requirement | [REQ_IN_03](requirements.md#req_in_03): MIO peripheral input `n` shall read the input of MIO pad `p`, in the same cycle, while `MIO_PERIPH_INSEL_n` is 2 + `p` and pad `p` is allowed for input `n`. Here `p` runs from 0 to `NMioPads` - 1. |
| Testpoint | [`pad_listen`](../../data/pinmux_env_fpv_testplan.hjson#pad_listen): every peripheral input reads what its select names. It covers [REQ_IN_01](requirements.md#req_in_01), [REQ_IN_02](requirements.md#req_in_02), [REQ_IN_03](requirements.md#req_in_03), [REQ_IN_04](requirements.md#req_in_04), [REQ_IN_05](requirements.md#req_in_05). |
| Checker | The input selection checker, the module that holds the assertions of `pad_listen` |
| Check | *reads selected pad*, one of the 5 checks of `pad_listen` (*reads tie 0*, *reads tie 1*, *reads selected pad*, *select without a pad reads 0*, *DIO reads its pad*) |
| Planned assertion | `assert_PadListen_ReadsSelectedPad` |
| Why the check proves the requirement | The check compares each MIO peripheral input with `mio_in_i[p]` in the same cycle while its select is 2 + `p`, for every `p` from 0 to `NMioPads` - 1. For an input with a pad list, the check runs only over the pads that the list allows. |

${"###"} Sources
Each requirement names its source: a section, a register or a configuration key of the documents below.
Where none of these documents states the rule, the requirement says so.

| Source | Documents | What the plan takes from them |
|---|---|---|
| The pinmux specification | [theory of operation](../theory_of_operation.md), [programmer's guide](../programmers_guide.md), [interfaces](../interfaces.md), [registers](../registers.md), [register description](../../data/pinmux.hjson) | The rules of every feature and register |
| The top | [top description](../../../../data/top_${topname}.hjson), [pinmux configuration](../../data/top_${topname}_pinmux.ipconfig.hjson), ${'' if topname in 'earlgrey'.split() else "Earl Grey's "}[top-level design document](../../../../../top_earlgrey/doc/design/README.md) | The pads and their types, the pad reset attributes, ${on(strap, 'the strap and JTAG pads, ')}the counts and select ranges, the clocks and resets |
| The neighbours | [power manager](../../../pwrmgr/doc/theory_of_operation.md), [reset manager](../../../rstmgr/doc/theory_of_operation.md), ${'' if topname in 'earlgrey darjeeling'.split() else "Earl Grey's "}[alert handler](../../../../../top_${topname if topname in 'earlgrey darjeeling'.split() else 'earlgrey'}/ip_autogen/alert_handler/doc/theory_of_operation.md)${on(strap, ', [life cycle controller](../../../../../ip/lc_ctrl/doc/theory_of_operation.md)')}${on(strap, ', [life cycle interfaces](../../../../../ip/lc_ctrl/doc/interfaces.md)')}${on(strap, ", [life cycle programmer's guide](../../../../../ip/lc_ctrl/doc/programmers_guide.md)")}${on(strap, ', [life cycle description](../../../../../ip/lc_ctrl/data/lc_ctrl.hjson)')}${on(strap, ', [device life cycle specification](../../../../../../doc/security/specs/device_life_cycle/README.md)')}${on(strap, ', [`rv_dm` interfaces](../../../../../ip/rv_dm/doc/interfaces.md)')}${on(usb, ', [usbdev](../../../../../ip/usbdev/doc/theory_of_operation.md)')}${on(usb, ', [usbdev interfaces](../../../../../ip/usbdev/doc/interfaces.md)')}${on(usb, ', [usbdev wake and resume](../../../../../ip/usbdev/doc/wake_resume.md)')}${on(usb, ', [usbdev register description](../../../../../ip/usbdev/data/usbdev.hjson)')} | What each neighbour sends the pinmux and expects back |
| Common rules | [comportability](../../../../../../doc/contributing/hw/comportability/README.md), [TL-UL](../../../../../ip/tlul/README.md), the TileLink specification 1.9.3, [reggen](../../../../../../util/reggen/README.md), [CIP library](../../../../../dv/sv/cip_lib/README.md) | Bus answers, register behaviour and alerts |
% if usb:
| Existing testplans | [existing pinmux FPV testplan](../../data/pinmux_fpv_testplan.hjson), ${'' if topname in 'earlgrey darjeeling'.split() else "Earl Grey's "}[chip testplan](../../../../../top_${topname if topname in 'earlgrey darjeeling'.split() else 'earlgrey'}/data/chip_testplan.hjson)${on(usb, ', [usbdev testplan](../../../../../ip/usbdev/data/usbdev_testplan.hjson)')}, ${'' if topname in 'earlgrey'.split() else "Earl Grey's "}[chip usbdev testplan](../../../../../top_earlgrey/data/ip/chip_usbdev_testplan.hjson) | A rule that no other document states, where an existing testplan describes the behaviour |
% else:
| Existing testplans | [existing pinmux FPV testplan](../../data/pinmux_fpv_testplan.hjson), ${'' if topname in 'earlgrey darjeeling'.split() else "Earl Grey's "}[chip testplan](../../../../../top_${topname if topname in 'earlgrey darjeeling'.split() else 'earlgrey'}/data/chip_testplan.hjson) | A rule that no other document states, where an existing testplan describes the behaviour |
% endif

${"###"} Check kinds
The testplan gives each check a kind:

| Kind | What it says |
|---|---|
| `forward` | When the cause happens, the design responds within the time that the requirement gives. |
| `backward` | The design responds only when the cause happened. |
| `both` | The output equals its expected value in every cycle, which covers both directions. |
| `legal` | The output stays inside its allowed values. |
| `stable` | The output does not change without its cause. |
% if strap or usb:
| `structure` | The check has no assertion and needs no proof. It reads from the design which reset each flop of a named part uses, and it fails when a flop uses a reset that the requirement does not allow. Its name is `check_<Testpoint>_<Check>` ([Reset structure checks](#reset-structure-checks)). |
% endif
% if usb or rram:
| `waits on a specification question` | The assertion has a name, but it decides nothing, because no specification states the behaviour. The row of its requirement says which behaviour that is. |
% endif

A check can have two kinds, such as `forward, backward`: it then says both things.
A check that is marked "(through other checks)" has no assertion of its own.
The assertions of other checks decide it, and its row names the requirements that they decide.

${"##"} Scope
${"###"} Features
The table names the part of the testbench that checks each feature of the pinmux.

| Feature | Checked by |
|---|---|
| Pad input selection | The input selection checker |
| Pad output selection, sleep retention and pad attributes | The pad output checker |
| Attribute locks, bus error handling and the fatal alert | The locks, bus and alert checker |
| The wakeup detectors | The wakeup checker |
% if usb:
| The USB wakeup module: its wiring, and what it does at its ports | The USB wakeup checker |
% endif
% if strap:
| Strap sampling, the latched debug enable and TAP selection${on(rram, ', the RRAM TAP included')} | The straps and TAPs checker |
% endif
| Register access rules: access type, reset value, lock and error causes | The CSR checker |
| The TL-UL protocol on the register bus | The TL-UL ABVIP |

[Testbench architecture](#testbench-architecture) describes each of these parts.

${"###"} Security countermeasures
The pinmux register description lists the security countermeasures of the pinmux.
OpenTitan's testplan for them is [`pinmux_sec_cm_testplan.hjson`](../../data/pinmux_sec_cm_testplan.hjson).
The table shows what each countermeasure is and which testpoints of this plan check the behaviour behind it.
These testpoints are due at stage V2S, except `bus`, which is due at stage V2 ([Sign-off criteria per stage](#sign-off-criteria-per-stage)).

% if strap:
Several names end in `INTERSIG.MUBI`.
Such a signal runs between two blocks and carries a multi-bit code: it is On at one 4-bit value and Off at another.
The requirements state what the pinmux does at every value of such a signal, not only at On and Off.

% endif
| Countermeasure | What it is | Testpoints |
|---|---|---|
| `BUS.INTEGRITY` | Every bus request carries an integrity code. The pinmux raises its fatal alert on a request with a wrong code. | `bus`, `alert` |
% if strap:
| `LC_DFT_EN.INTERSIG.MUBI` | The life cycle DFT enable, a multi-bit input. It gates the DFT straps and the DFT TAP. | `strap`, `dft_strap`, `jtag` |
| `LC_HW_DEBUG_EN.INTERSIG.MUBI` | The life cycle hardware debug enable, a multi-bit input. The pinmux latches it, and the latched value gates the RISC-V TAP. | `strap`, `latch`, `jtag` |
| `LC_HW_DEBUG_CLR.INTERSIG.MUBI`, `LC_CHECK_BYP_EN.INTERSIG.MUBI`, `LC_ESCALATE_EN.INTERSIG.MUBI` | Three multi-bit life cycle inputs. Each one turns the latched debug enable Off. | `latch` |
| `PINMUX_HW_DEBUG_EN.INTERSIG.MUBI` | The latched debug enable, a multi-bit output to `rv_dm`. It keeps its value through a non-debug module reset. | `latch`, `jtag` |
| `TAP.MUX.LC_GATED` | The TAP selection. A TAP is connected to the JTAG pads only while the life cycle signal that gates it is On. | `jtag`, `jtag_pad` |
% endif
% if rram:
| `LC_NVM_DEBUG_EN.INTERSIG.MUBI` | The life cycle NVM debug enable, a multi-bit input. It gates the RRAM TAP. | `rram_tap` |
% endif

${"###"} Out of scope
The plan leaves out the cases below.
Each point gives the reason.

* **The TL-UL integrity functions.**
  The environment computes the integrity codes it expects with the same functions that the design uses.
  It therefore checks that the pinmux rejects a wrong code and raises its alert.
  It does not check that the functions compute the right code.
  The FPV testbenches of the two codes, [`prim_secded_inv_64_57`](../../../../../ip/prim/fpv/tb/prim_secded_inv_64_57_tb.sv) and [`prim_secded_inv_39_32`](../../../../../ip/prim/fpv/tb/prim_secded_inv_39_32_tb.sv), check that the decoder flags every single-bit and double-bit error.
% if scan_clk:
* **A wakeup detector on a scan clock pad while scan mode is on.**
  A scan clock pad carries the scan clock while scan mode is on.
  No specification says what a wakeup detector watches on such a pad during that time.
  The wakeup checks therefore do not cover a detector while scan mode is on and the detector watches a scan clock pad.
% endif
% if strap:
* **The TRST_N of a connected TAP while scan mode is on.**
  With scan mode off, the TRST_N that a connected TAP receives follows the TRST_N pad, and the plan checks this.
  No specification says which reset this TRST_N follows while scan mode is on, so the plan has no requirement and no check for that case.
% endif
* **A reset during a run.**
  Each proof applies every reset once, at the start ([Constraints](#constraints)).
  The proofs therefore do not show what the pinmux does when a reset arrives later.
% if strap or usb:
  For the requirements that depend on a later reset, a check of the design's structure shows which flops that reset reaches ([Reset structure checks](#reset-structure-checks)).
% endif
% if strap:
* **What a peripheral reads from a JTAG pad while a TAP owns the pad.**
  While a TAP is connected, the JTAG pads carry that TAP's signals.
  No specification says what a peripheral reads from such a pad during that time.
  The plan has no check for this case.
* **A JTAG pad in sleep while a TAP owns the pad.**
  No specification says whether such a pad keeps the TAP's signal or takes its sleep value when the chip goes to sleep.
  The plan has no check for this case.
% endif

${"##"} Testbench architecture
This is the planned architecture.
The environment instantiates the whole `pinmux` RTL, with its real register block and ${top_title}'s pad configuration (pad types and pad roles).
It binds one top-level checker, `pinmux_fpv_env`, to the pinmux.
The top-level checker holds every assertion, assumption and cover of the plan, and every other checker sits inside it.
A bound module is attached to the design and reads its signals, and the design itself stays unchanged.
The top-level checker reads every pinmux port and these internal signals:

* the register values (`reg2hw`, `hw2reg`) and every lock register;
* the always-on side's write of `WKUP_CAUSE`${on(strap, ' and the sampled TAP straps')}${';' if usb else '.'}
% if usb:
* the ports, clock and reset of the USB wakeup module.
% endif


![The FPV environment, drawn for Earl Grey: the pinmux RTL and the top-level checker bound to it, the blocks each checker inside it watches, and the TAP-ownership signal the straps and TAPs checker sends the pad checkers](pinmux_fpv_tb.svg)

The top-level checker has two shared parts and one checker per feature.
The shared parts are described first.

${"###"} TL-UL ABVIP
`tlul_abvip` is a set of TL-UL protocol assertions for formal, new with this environment.
ABVIP stands for assertion-based verification IP.
It does two jobs on the pinmux's bus port:

* **Protocol rules.**
  It assumes that the host keeps the TL-UL handshake on `tl_i`.
  It limits the host's requests only in the mask, so a request can be legal or illegal ([Assumptions](#assumptions)).
  It asserts that the pinmux follows the TL-UL rules on `tl_o`.
* **Bus monitor.**
  To check the protocol, the ABVIP follows each request from the cycle the pinmux accepts it to the cycle the pinmux answers it.
  The bus monitor is the part of the ABVIP that reports this to the checkers.
  For each write it reports the address, the data and the byte mask, and whether the pinmux answered without an error.

The checks of the locks, the alert test, the wakeup mode and a failed write read the bus monitor to know what software wrote.
% if rram:
The check that the RRAM TAP stays cut until software writes its register reads it too.
% endif
One instance of the ABVIP sits on the pinmux's bus port in every checker proof.
A second instance sits inside the CSR checker, in the register block proof.

${"###"} CSR checker
The CSR checker proves the register block.
For every register it checks the access type, the reset value and the lock.
It also checks the answer to every cause of a bus error.

The checker keeps a mirror, which is its own copy of every register field.
It updates the mirror on each write that software makes over the bus and on each write that hardware makes.
The mirror therefore holds the value that each field must have and the value that each read must return, whichever side wrote last.
The checker's assertions compare the register block with the mirror.

reggen already generates a CSR checker from the register description.
The CSR checker of this plan extends it, as the table shows.

| Covered | reggen's generated checker | The CSR checker of this plan |
|---|---|---|
| Registers | The registers that hardware cannot write | Every register. In the pinmux this adds the pad attribute, sleep status and wakeup cause registers, which hardware writes. |
| Error causes | One: a request to an address that no register maps | Every cause |

The extension is a change to reggen's generator.
That change is made and reviewed on its own, and this plan depends on it.
The testpoint `register_block` references that change when it is merged.
Where a requirement's *Checked by* names the CSR checker, it means the extended checker.
The testpoint `register_block` holds the requirements that the extended checker decides.
The imported testpoint `fpv_csr_rw` describes the generated checker without the extension.

For two kinds of pinmux register the mirror alone is not enough.
The CSR checker has one more check for each kind, and a feature checker covers what is left.

| Register | Why the mirror is not enough | What the CSR checker checks | What a feature checker checks |
|---|---|---|---|
| Pad attribute registers | The register block does not store them (`hwext`). The pinmux logic stores the value and supplies it for every read. | A write reaches the pinmux logic in the cycle the register block accepts it. A read returns the value that the pinmux logic supplies in that cycle. | The supplied value is the right one (the checks of `pad_attr`). |
| Wakeup detector registers, except `WKUP_DETECTOR_PADSEL` | The detectors run on the always-on clock, so each write crosses from `clk_i` to `clk_aon_i` (`async`). | The register block answers a bus access to such a register only after the previous write to it has reached the always-on side. | Each write reaches the always-on logic in time and in order (the checks of `wakeup_sync`). |

${"###"} Feature checkers
| Checker | What it checks | Testpoints it proves | Its assertions are repeated per |
|---|---|---|---|
| Input selection checker | The input selection of every MIO and DIO peripheral input, with the pad list and the reset selection of each input | `pad_listen`, `sparse_insel`, and the input check of `reset_state` | MIO pad (${n_mio_pads}) |
| Pad output checker | The output mux, sleep retention and pad attributes, with the pad list of each output and the reset selection of each pad | `pad_output`, `sparse_outsel`, `pad_sleep`, `pad_attr`, and the pad check of `reset_state` | Pad, MIO and DIO |
| Locks, bus and alert checker | The attribute locks; the bus answers, failed requests and the fatal alert | `regwen`, `bus`, `alert`; in `bus`, the protocol check is the TL-UL ABVIP's and the two checks marked "(through other checks)" follow from the CSR checker | Attribute lock (${n_mio_pads + n_dio_pads}) |
| Wakeup checker | The wakeup detectors, their cause bits and the wakeup request | `wakeup`, `wakeup_cause`, `wakeup_sync` | Detector (${n_wkup_detect}) |
% if usb:
| USB wakeup checker | Each port of the USB wakeup module carries the pinmux signal of the same role; the module takes over the pull-ups, reports its three events and requests the wakeup as usbdev's specification says | `usb_conn`, `usb_module` | - |
% endif
% if strap:
| Straps and TAPs checker | Strap sampling, the DFT straps, the latched debug enable, TAP selection and the JTAG pads | `strap`, `dft_strap`, `latch`, `jtag`, `jtag_pad`${on(rram, ', `rram_tap`')} | TAP (${3 + int(rram)}) |
% endif

The last column says what each checker repeats its assertions for.
The formal tool proves each copy on its own, so a failure names the exact pad, lock${', detector or TAP' if strap else ' or detector'}.
The attribute locks are checked here, and the CSR checker checks every other lock.
Each assertion has the name that its check plans, such as `assert_PadListen_ReadsSelectedPad`, and a comment that names its requirements and its testpoint.
The testpoint `sleep_release` has no assertions of its own.
It follows from the checks of the testpoints above, and the testplan says how.

% if strap:
${"###"} TAP ownership
While a TAP is connected, the five JTAG pads carry that TAP's signals and the pad muxes do not drive them.
The straps and TAPs checker works out, for each TAP, whether that TAP may own the JTAG pads in the current cycle.
It uses the sampled straps, the latched debug enable and the DFT enable input.
% if rram:
For the RRAM TAP it also uses the NVM debug enable input and the register `RRAM_JTAG_SEL`.
% endif
The input selection and pad output checkers apply their checks to a JTAG pad only while no TAP may own it.

% endif
% if strap or usb:
${"###"} Reset structure checks
Some requirements say which reset a part of the pinmux uses, or that a reset leaves a part unchanged.
A proof cannot show this here, because each proof applies every reset once, at the start ([Constraints](#constraints)).
The plan checks these requirements on the structure of the design instead.
Such a check has the kind `structure` in the testplan and is not an assertion.
The setup of the formal run does it in three steps:

1. It finds every flop of the part that the check names.
2. For each flop it reads which reset the flop uses.
   Where the check asks for it, it also follows the flop's data inputs back to every signal that can reach them.
3. It stops the run with an error when it finds a reset that the requirement does not allow.
   It also stops when the part has no flop, because a check of an empty part passes and proves nothing.

| Part of the design | What the check requires | Testpoints |
|---|---|---|
% if strap:
| The sampled TAP straps, the latched debug enable and the TAP selection | None of the resets that a non-debug module (NDM) reset asserts reaches these flops, through a reset input or through a data input. These values therefore survive an NDM reset. | `strap`, `latch`, `jtag` |
% endif
% if usb:
| The USB wakeup module | Every flop takes its reset from `rst_aon_ni`. | `usb_conn` |
% endif
% endif

${"###"} Reference value sources
Each assertion compares the design with a reference value, for example the address of a register or the reset value of a pad attribute.
If a checker took such a value from the RTL, a wrong value in the RTL would be wrong on both sides, and the assertion would still pass.
The environment therefore takes its reference values from the descriptions that the RTL is generated from.

| Reference value | Where the environment takes it from |
|---|---|
| Register offsets and field positions | The register order and field layout of the register description, `pinmux.hjson` |
| Pad and peripheral counts, and pad attribute reset values | The top's pinmux configuration, `top_${topname}_pinmux.ipconfig.hjson`, which topgen writes from the top description |
| ${'The JTAG pads, the strap pads and the pad types' if strap else 'The pad types'} | The top description, `top_${topname}.hjson` |
| TL-UL integrity codes | The integrity functions of `tlul_pkg`, in the RTL |

The integrity codes are the one reference value that a checker computes with the RTL's own functions, which is why the integrity functions are [out of scope](#out-of-scope).
A requirement of kind `RTL`, or a part of a requirement that carries the mark (*RTL*: ...), is a different case.
Such a requirement writes the design's present behaviour down as a fixed rule, and the checker holds the design to that rule.
The environment also uses the RTL's type definitions of the ports and the register structs, to connect to the design.

${"##"} Verification strategy
Three words describe how the proofs are set up:

* An **abstraction** lets a part of the design, or its start state, take more values than it really can, so that one proof covers more cases.
  It removes no real behaviour.
* A **constraint** narrows what the proofs explore.
  Each constraint says what it leaves unchecked.
* An **assumption** is a rule that the environment makes the inputs of the pinmux follow.
  Each assumption names the document that gives the rule, or says that no specification gives it.

${"###"} Proofs
The checks are proven in separate proofs.
Each proof runs on the whole design and holds the assertions its row names, with the assumptions they need.

| Proof | Checker | Testpoints | Start state and setup |
|---|---|---|---|
| Register block | CSR checker | `register_block` | The registers start from reset |
| Input selection | Input selection checker | `pad_listen`, `sparse_insel` | The register fields start from any value |
| Pad output | Pad output checker | `pad_output`, `sparse_outsel`, `pad_sleep`, `pad_attr` | The register fields start from any value |
| Locks, bus and alert | Locks, bus and alert checker | `regwen`, `bus`, `alert` | The registers start from reset |
| Wakeup | Wakeup checker | `wakeup`, `wakeup_cause`, `wakeup_sync` | The register fields on `clk_i` start from any value; the detector locks start from reset |
% if usb:
| USB wakeup | USB wakeup checker | `usb_conn`, `usb_module` | The registers start from reset |
% endif
% if strap:
| Strap sampling | Straps and TAPs checker | `strap`, `dft_strap` | The register fields start from any value |
| TAP selection | Straps and TAPs checker | `latch`, `jtag`, `jtag_pad`${on(rram, ', `rram_tap`')} | The registers start from reset; the sampled TAP straps are free |
% endif
| Reset values | Input selection and pad output checkers | `reset_state`, and the checks of `pad_attr` and `pad_sleep` on the state immediately after reset | The registers start from reset |
| The design's own assertions | None: the assertions written in the RTL | - | The registers start from reset; reported apart from the checkers |

A proof that starts from any register value never sees the reset values.
The checks on the state immediately after reset therefore have a proof of their own, the Reset values row.

${"###"} Abstractions
No abstraction edits the RTL.
The column Start state and setup of [Proofs](#proofs) shows which proof uses each one.

| Abstraction | Why the result holds for the design | What another check covers |
|---|---|---|
| The register fields start from any value: each field that only software writes starts with any value. A field that hardware writes, or that is on the always-on clock, starts from reset. | The start values include every setting that software can write from reset. | The Reset values proof and the Register block proof start from reset and check the reset values. |
% if strap:
| The sampled TAP straps are free: they take any value in any cycle. | Every value that the strap sampling can produce is among the free values. | The Strap sampling proof checks that the pinmux samples the right value. |
% endif

${"###"} Constraints
The last sentence of each constraint says what it leaves unchecked.

* **`clk_aon_i` runs five times slower than `clk_i`.**
  The always-on clock is the slow clock ([Wakeup Features](../programmers_guide.md#wakeup-features)), and the assertions inside the clock-crossing primitive are written for this ratio.
  A check that involves the always-on clock is proven at this ratio only.
  The proofs do not show the pinmux while `clk_i` is stopped.
* **Each reset is applied once, at the start.**
  A reset that can arrive in any cycle multiplies the states that the tool must explore.
% if strap or usb:
  A structure check shows which flops a reset reaches ([Reset structure checks](#reset-structure-checks)).
% endif
  The proofs do not show what a later reset does.
% if strap:
* **Scan mode is off in two groups of checks** (`scanmode_i`).
  The first group checks a wakeup detector that watches a scan clock pad.
  The second group checks that the TRST_N of a connected TAP follows its pad.
  No specification says what the pinmux does in these two cases while scan mode is on ([Out of scope](#out-of-scope)).
  Scan mode is free in every other check.
  The proofs do not show these two cases while scan mode is on.
% else:
% if scan_clk:
* **Scan mode is off in the checks of a wakeup detector that watches a scan clock pad** (`scanmode_i`).
  No specification says what such a detector watches while scan mode is on ([Out of scope](#out-of-scope)).
  Scan mode is free in every other check.
  The proofs do not show such a detector while scan mode is on.
% endif
% endif
* **No signal integrity error on the alert lines.**
  The environment keeps each signal pair of the alert handler complementary ([Assumptions](#assumptions)).
  The plan does not check how the alert sender answers a pair that is not complementary.
* **No in-band reset of the alert handler.**
  The in-band reset is the alert handler's re-initialization.
  During it, the alert handler puts a signal integrity error on its signal pairs on purpose (${'' if topname in 'earlgrey darjeeling'.split() else "Earl Grey's "}[Employed Solution](../../../../../top_${topname if topname in 'earlgrey darjeeling'.split() else 'earlgrey'}/ip_autogen/alert_handler/doc/theory_of_operation.md#employed-solution)).
  The proofs do not show the pinmux during an in-band reset.

${"###"} Assumptions
Each assumption models a neighbour of the pinmux.
**Models** names the neighbour and the source of the rule, and **Why** says what the proofs need it for.
Every other input is free${on(scan_clk, ', except scan mode in the cases that [Constraints](#constraints) names')}.

* **The bus host holds each request until the pinmux takes it, and has at most one pending request per source ID** (`tl_i`).
  * **Models:** the bus host, under the rules of the [TL-UL protocol checker](../../../../../ip/tlul/doc/TlulProtocolChecker.md).
    Its requests are free, legal and illegal: the opcode, the size, the address and the integrity codes take any value.
  * **Why:** a host that broke the handshake would make the bus checks fail for a reason outside the pinmux.
    The free requests let the proofs reach every error cause and every failed request.
* **The bus host sends contiguous masks only** (`tl_i`).
  * **Models:** the hosts of OpenTitan, which do not send a non-contiguous mask ([Usage of Opcode, Size and Mask](../../../../../ip/tlul/README.md#usage-of-opcode-size-and-mask)).
  * **Why:** a device may answer a non-contiguous mask with an error or not ([Usage of Opcode, Size and Mask](../../../../../ip/tlul/README.md#usage-of-opcode-size-and-mask)), so no document fixes the pinmux's answer.
    A request with a non-contiguous mask is therefore not checked.
* **The alert handler follows the alert protocol** (`alert_rx_i`): it keeps its signal pairs complementary, follows the four-phase handshake, and sends a new ping at least 4 cycles after the previous handshake is complete.
  * **Models:** the alert handler (${'' if topname in 'earlgrey darjeeling'.split() else "Earl Grey's "}[Differential Alert Signaling](../../../../../top_${topname if topname in 'earlgrey darjeeling'.split() else 'earlgrey'}/ip_autogen/alert_handler/doc/theory_of_operation.md#differential-alert-signaling), ${'' if topname in 'earlgrey darjeeling'.split() else "Earl Grey's "}[LFSR Timer](../../../../../top_${topname if topname in 'earlgrey darjeeling'.split() else 'earlgrey'}/ip_autogen/alert_handler/doc/theory_of_operation.md#lfsr-timer)).
    No specification bounds its time to answer, so the environment answers each phase of the handshake within 8 `clk_i` cycles.
  * **Why:** a handler that broke the protocol would make a correct alert sender fail its checks.
    The alert sender waits for each answer before it continues, so the alert checks need a bound.
* **The sleep input changes on `clk_i`** (`sleep_en_i`).
% if eg_top:
  * **Models:** the power manager, which runs on the same clock as the pinmux ([top_${topname}.hjson${eg(' `module.pwrmgr.clock_srcs clk_i`')}](../../../../data/top_${topname}.hjson), [top_${topname}.hjson${eg(' `module.pinmux clock_srcs`')}](../../../../data/top_${topname}.hjson)).
% else:
  * **Models:** the power manager. No specification names the clock of this input.
% endif
  * **Why:** the pinmux registers this input on `clk_i`.
% if strap:
* **The strap pulse comes once per boot, and is one `clk_i` cycle wide** (`strap_en_i`).
  * **Models:** the power manager, which never sends the pulse after an NDM reset (${'' if topname in 'earlgrey englishbreakfast'.split() else "Earl Grey's "}[Non-debug Module Reset](../../../../../top_${topname if topname in 'earlgrey englishbreakfast'.split() else 'earlgrey'}/ip_autogen/pinmux/doc/theory_of_operation.md#non-debug-module-reset)).
    No specification gives the width of the pulse, so the environment uses the width that the design's own input assumption expects.
  * **Why:** the pinmux samples the straps and the debug enable on each pulse.
    A pulse after an NDM reset would sample them again, which the power manager never does.
% endif
* **Software turns a wakeup detector off before it changes the detector's mode** (`tl_i` writes).
  * **Models:** software, which the theory of operation tells to turn the detector off first ([Wakeup Detectors](../theory_of_operation.md#wakeup-detectors)).
  * **Why:** the pinmux does not clear the detector's counter on a mode change, so no document says what a detector that is on does after one.
    The proofs therefore do not show a mode change on a detector that is on.
% if usb:
* **usbdev's pull-up enables do not change in the 4 always-on cycles before a suspend request** (`usbdev_dppullup_en_i`, `usbdev_dnpullup_en_i`).
  * **Models:** usbdev, which activates the USB wakeup module only in the Suspended state ([Optional external AON/Wake functionality](../../../../../ip/usbdev/doc/theory_of_operation.md#optional-external-aonwake-functionality)).
    No specification gives this number of cycles.
  * **Why:** the USB wakeup module takes over the pull-ups in one step.
    An enable that changed just before the request would leave no single correct value to take over.
% endif

The checker proofs do not use the assumptions that are written in the design (`PinmuxWkupStable_A`${on(strap, ', `PwrMgrStrapSampleOnce0_A`, `PwrMgrStrapSampleOnce1_A`')}).

${"###"} Vacuity and covers
An assertion is vacuous when its trigger never happens: it then passes without checking anything.
Covers guard against this, and every proof runs its covers before its assertions.
Every proof has at least these covers:

* **Precondition covers**, one per assertion, show that the assertion's trigger can happen.
* **Witness covers**, one per assumption and constraint, show that the environment still allows the legal case it is about, so the environment is not over-constrained.

The wakeup proof also has covers for the cases that need the most cycles: a wakeup count of ${2 ** wkup_cnt_width - 1} and the wrap of the counter, about ${2 ** wkup_cnt_width + 4} always-on cycles.
A requirement does not close while one of its covers is unreached ([Sign-off criteria per stage](#sign-off-criteria-per-stage)).

${"###"} Sign-off criteria per stage
The stages are OpenTitan's [verification stages for FPV](../../../../../../doc/project_governance/development_stages.md), which give the full criteria.
A requirement closes when its checks are proven, their covers are reached, and every check that the abstractions of its proof rely on is proven ([Abstractions](#abstractions)).
Each constraint of its proof must be lifted, or recorded with what it leaves unchecked ([Constraints](#constraints)).

| Stage | OpenTitan's main criteria | In this plan |
|---|---|---|
| V1 | Testplan reviewed, assertions bound, the main functional path proven. | `pad_listen` and `pad_output`: the pad data path, which is the pinmux's main functional path, with the TL-UL ABVIP bound. |
| V2 | Every assertion written, assumptions reviewed, 90 % proven, 90 % code and 75 % cone-of-influence coverage. | Every other functional testpoint, the CSR checker, and the device rules of the TL-UL ABVIP. The plan's own target is 100 % cone-of-influence coverage. |
| V2S | The checks of the security countermeasures pass. | The testpoints of the fatal alert${on(strap, ', strap sampling, the DFT straps, the latched debug enable, TAP selection and the JTAG pads')}${on(rram, ', and the RRAM TAP')}. |
| V3 | Every assertion proven, 100 % code and cone-of-influence coverage. | Every testpoint. |

${"##"} Building and running tests
The environment's [dvsim](https://github.com/lowRISC/dvsim) entry has the name `pinmux_env_fpv`.
The entry is added to the formal configuration${eg(' of Earl Grey')} together with the environment's code.

${"##"} Requirements
[requirements.md](requirements.md) holds the ${n(133, 26, 41, 8)} requirements, for reading.
[`pinmux_fpv_requirements.hjson`](../../data/pinmux_fpv_requirements.hjson) holds the same rows as data.
${n(126, 26, 40, 7)} of them state a rule the specification gives (kind `spec`).
${n(7, 0, 1, 1)} state a rule that no specification gives (kind `RTL`).
${n(6, 5, 1, 2)} of the `spec` rows mark one part of their rule that no specification gives.
These follow the design's present behaviour.



${"##"} Testplan
[Testplan](../../data/pinmux_env_fpv_testplan.hjson)
