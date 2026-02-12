# SoC Proxy Technical Specification

SoC Proxy is a simple comportable IP module that facilitates the breakout of signals and buses internal to OpenTitan (similar to Sensor Control for AST).

## Comportable Interfaces

- Clock / reset (intended for connection to the fast clock domain)
- 1 TL-UL Device port for comportable CSR node
- 1 TL-UL Device port with an address range to egress into CTN
- 1 Fatal alert for bus integrity
- 2 Wakeup requests
  - Internal wakeup request, should be asserted whenever an external alert or IRQ is seen
  - External wakeup request

## SoC-facing interfaces

- Synchronous interfaces:
  - 1 TL-UL Host port for egress into CTN
  - 1 Wakeup request, asynchronous and level-encoded
  - 32 Interrupts, asynchronous and level-encoded
  - 16 general-purpose inputs
  - 16 general-purpose outputs
