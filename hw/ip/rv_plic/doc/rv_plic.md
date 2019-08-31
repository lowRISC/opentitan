{{% lowrisc-doc-hdr Interrupt Controller Technical Specification }}
{{% regfile rv_plic.hjson }}

{{% section1 Overview }}

This document specifies the Interrupt Controller (RV_PLIC) functionality. This
module conforms to the
[Comportable guideline for peripheral functionality.](../../../../doc/rm/comportability_specification.md)
See that document for integration overview within the broader top level system.

{{% toc 3 }}

{{% section2 Features }}

- RISC-V Platform-Level Interrupt Controller (PLIC) compliant interrupt controller
- Support arbitrary number of interrupt vectors (up to 256) and targets
- Support interrupt enable, interrupt status registers
- Memory-mapped MSIP register per HART.

{{% section2 Description }}

The RV_PLIC module is designed to manage various interrupt sources from the
peripherals. It receives interrupt events and detects edge or level of the
signals then notifies the multiple targets within the RISC-V core.

{{% section2 Compatibility }}

The RV_PLIC is compatible with any RISC-V core implementing the RISC-V privilege specification.

{{% section1 Theory of Operations }}

{{% section2 Block Diagram }}

![RV_PLIC Block Diagram](block_diagram.svg)

{{% section2 Details }}

### Identifier

Each interrupt source has a unique ID assigned based upon its bit position
within the input `intr_src_i`. ID counting ranges from 1 to N, the number of
interrupt sources. `intr_src_i[i]` bit has an ID of `i+1`. This ID is used when
targets “claim” the interrupt and to “complete” the interrupt event.

### Priority and Threshold

Interrupt sources also have configurable priority values. The maximum value of
the priority is configurable through the Verilog parameter `MAX_PRIO`. RV_PLIC
chooses the highest priority interrupt among the pending interrupts if its value
exceeds the threshold for the target.

Each target can configure the threshold value. Only interrupts that have
priorities greater than the threshold are forwarded to the target. So, if a
target wants to not receive any interrupts, it can configure threshold to the
max value if turning off all interrupt sources requires multiple register
writes.

`MAX_PRIO` parameter is most area contributing option in RV_PLIC. If `MAX_PRIO`
is big, then finding the highest priority in Process module consumes a lot of
logic gates.

### Interrupt Gateways

Gateway module converts interrupt events from the peripherals to a common
interrupt request format used in RISC-V PLIC. It is configurable to detect the
interrupt event when the signal is changed from 0 to 1 (edge-triggered) or to
notify every time when the signal is 1 (level). Gateway forwards the new
interrupt request only after one of the targets claims the interrupt and
completes it. If a target claims the interrupt event, Gateway de-asserts
interrupt request (Interrupt Pending bit) but doesn't set IP, even it detects
event from the peripheral. Gateway module in RV_PLIC doesn't support counter for
edge-triggered event. Any events happen in the time from claimed to completed
are ignored.

### Interrupt Enables

Each target has a set of Interrupt Enable (`IE`) registers. Each bit in the IE
registers controls the corresponding interrupt source. RV_PLIC doesn't have
global interrupt turn-on and off feature.

### Interrupt Claims

"Claiming" an interrupt is done by a target reading the associated
Claim/Completion (`CC`) register for the target. The return value of the !!CC
read represents the pending interrupt that has the highest priority. If two or
more pending interrupts have the same priority, RV_PLIC chooses the one with
lowest ID.

### Interrupt Completion

After an interrupt is claimed, the interrupt pending (`IP`) bit of the interrupt
source is cleared, regardless of the status of the `intr_src_i` input value.
Until a target “completes” the interrupt, it won't be re-set if a new event
for the interrupt occurs. A target completes the interrupt by writing the ID of
the interrupt to the !!CC register. The write event is forwarded to the Gateway
logic, which resets the interrupt status to accept new interrupt event. The
assumption is that the processor has cleaned up the originating interrupt event
during the time between claim and complete such that the `intr_src_i[ID-1]`
value is no longer true.

~~~~wavejson
{ signal: [
  { name: 'clk',           wave: 'p...........' },
  { name: 'intr_src_i[i]', wave: '01.....0..1.', node:'.....a....b' },
  { name: 'irq_o',         wave: '0.1.0......1', node:'.....c.....d'},
  { name: 'irq_id_o',      wave: '=.=.=......=',
                           data: ["0","i+1","0","i+1"] },
  { name: 'claim',         wave: '0..10.......'},
  { name: 'complete',      wave: '0.......10..', node:'........e...'},
  ],
  head:{
    text: 'Interrupt Flow',
    tick: 0,
  },
}
~~~~


{{% section2 Hardware Interfaces }}

{{% hwcfg rv_plic }}

{{% section1 Programmers Guide }}

{{% section2 Initialization }}

After reset, RV_PLIC doesn't generate any interrupts to any targets even if
interrupt sources are set, as the priorities and thresholds are 0 by default and
all IE values are 0. Software should configure the above three registers and the
interrupt source type !!LE .

!!LE and !!PRIO0 .. !!PRIO31 registers are unique. So, only one of the targets
shall configure them.

~~~~c
// Pseudo-code below
void plic_init() {
  // Set to level-triggered for interrupt sources
  for (int i = 0 ; i < ceil(N_SOURCE/32) ; i++) {
    *(LE+i) = 0;

  // Configure priority
  for (int i = 0 ; i < N_SOURCE ; i++) {
    *(PRIO+i) = value(i);

}

void plic_threshold(tid, threshold) {
  *(THRESHOLD+tid) = threshold;
}

void plic_enable(tid, iid) {
  // iid: 0-based ID
  int offset = ceil(N_SOURCE/32) * tid + (iid>>5);

  *(IE+offset) = *(IE+offset) | (1<<(iid%32));
}
~~~~

{{% section2 Handling Interrupt Request Events }}

If software receives an interrupt request, it is recommended to follow the steps
shown below.

1. Claim right after entering to the interrupt service routine by reading !!CC
   register.
2. Determine which interrupt should be serviced based on read-out !!CC register.
3. Execute ISR, clear originating peripheral interrupt.
4. Write Interrupt ID to !!CC
5. Repeat as necessary for other pending interrupts.

It is possible to have multiple interrupt events claimed. If software claims one
interrupt request, then the process module advertises any pending interrupts
with lower priority unless new higher priority interrupt events occur. If a
higher interrupt event occurs after previous interrupt is claimed, the RV_PLIC
IP advertises the higher priority interrupt. Software may utilize an event
manager inside a loop so that interrupt claiming and completion can be
separated.

~~~~c
void interrupt_service() {
  // tid is predefined value.
  uint32 iid;
  iid = *(CC + tid);
  if (iid == 0) {
    // Interrupt is claimed by one of other targets
    return ;

  do {
    // Process interrupts
    // ...

    // Complete
    *(CC + tid) = iid;
    iid = *(CC + tid);
  } while (iid != 0);
}
~~~~

{{% section2 Registers }}

Register description can be generated with `reg_rv_plic.py` script. The reason
of having yet another script for register is that PLIC is configurable to the
number of input sources and output targets. To implement it, some of the
registers (see below **IE**) should be double nested in register description
file. As of Jan. 2019, `regtool.py` supports only one nested multiple register
format `multireg`.

Below register description doesn't match with Top Earlgrey RV_PLIC design. The
RV_PLIC in the top_earlgrey is generated by topgen tool so that the number of
interrupt sources is different.

-   LE: CEILING(N_SOURCE / DW)
    Value 1 indicates the interrupt source's behavior is edge-triggered It is
    used in the gateways module.
-   IE: CEILING(N_SOURCE / DW) X N_TARGET
    Each bit enables corresponding interrupt source. Each target has IE set.
-   PRIO: N_SOURCE
    Universal set across all targets. Lower n bits are valid. n is determined by
    MAX_PRIO parameter
-   THRESHOLD: N_TARGET
    Priority threshold per target. Only priority of the interrupt greater than
    threshold can raise interrupt notification to the target.
-   IP: CEILING(N_SOURCE / DW)
    Pending bits right after the gateways. Read-only
-   CC: N_TARGET
    Claim by read, complete by write

{{% registers x }}

