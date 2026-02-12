# OpenTitan Darjeeling (Integrated Admissible Architecture) Datasheet

## Overview

OpenTitan Darjeeling is a system-on-a-chip Secure Execution Environment, capable of serving as a root of trust (RoT) for measurement and attestation among other applications, for instantiation within a larger system.
It can serve as the SoC root of trust, a platform root of trust, or even be integrated and leveraged for individual chiplet RoTs.

![Top Level Block Diagram](top_darjeeling_block_diagram.svg)

Darjeeling's block diagram shows the system configuration, including the RISC-V Ibex processor and all of the memories and comportable peripheral IPs.
The system is split into a high speed domain (e.g. 1 GHz clock in a recent process node) and a peripheral domain (e.g. 250 MHz).
The system has support for light sleep only, since the entire root-of-trust is expected to be always-on in an integrated context.

The SoC integration wrapper contains shared infrastructure that can be adapted based on the integrator's needs.
It contains a control network (CTN) crossbar for attaching shared SoC-level peripherals, as well as a large, shared CTN SRAM.

Communication with the SoC is mainly via the mailboxes, DMA and SoC proxy module.
The SoC proxy module serves as a comportable IP frontend for incoming IRQs, reset requests, wake up requests, alerts and the TL-UL egress port into the CTN network.
Egress TL-UL requests go through base address translation and range-based access control checks, which provides flexibility and isolation in the CTN space.
Code can be executed from both internal memories (ROM partitions 1 and 2, main SRAM) and CTN SRAM.

Debug access is established via the JTAG TAP attached to a debug TL-UL crossbar.
Through that, a JTAG mailbox, the RISC-V debug module, the SoC debug controller, and the life cycle controller can be accessed.
The JTAG mailbox can be used to implement firmware-driven SoC-level debug authorization.
Infrastructure signals such as clocks, resets and the entropy source are provided by the analog sensor top (AST) block, which is connected to the Darjeeling-internal power, clock and reset manager blocks.
The sensor control block provides a comportable IP front-end for the AST block that the Ibex processor can interact with.

The following table provides a more detailed summary of the supported features:

<table>
<thead style='font-size:100%'>
  <tr>
    <th colspan="2">OpenTitan Darjeeling Features</th>
  </tr>
</thead>
<tbody style='font-size:90%;line-height:110%'>
  <tr>
    <td>
      <ul>
        <li>RV32IMCB RISC-V "Ibex" core:
          <ul>
            <li>3-stage pipeline, single-cycle multiplier</li>
            <li>Support for the full ratified bit manipulation extension and some unratified subsets</li>
            <li>4 KiB instruction cache with 2 ways</li>
            <li>RISC-V compliant JTAG DM (debug module)</li>
            <li>PLIC (platform level interrupt controller)</li>
            <li>U/M (user/machine) execution modes </li>
            <li>Enhanced Physical Memory Protection (ePMP) with 16 regions</li>
            <li>Address translation with 32 regions</li>
            <li>Security features:
              <ul>
                <li>Low-latency memory scrambling on the icache</li>
                <li>Dual-core lockstep configuration</li>
                <li>Data independent timing</li>
                <li>Dummy instruction insertion</li>
                <li>Bus and register file integrity</li>
                <li>Hardened PC</li>
              </ul>
            </li>
          </ul>
        </li>
        <br></br>
        <li>Security peripherals:
          <ul>
            <li>AES-128/192/256 with ECB/CBC/CFB/OFB/CTR modes</li>
            <li>HMAC / SHA2-256, 384, 512</li>
            <li>KMAC / SHA3-224, 256, 384, 512, [c]SHAKE-128, 256</li>
            <li>Programmable big number accelerator for RSA and ECC (OTBN)</li>
            <li>NIST-compliant cryptographically secure random number generator (CSRNG)</li>
            <li>Entropy source, with FIPS- and CC-compliant health checks, which can be bypassed depending on the properties of the connected digital noise source</li>
            <li>Key manager with DICE & DPE support</li>
            <li>Manufacturing life cycle manager</li>
            <li>Alert handler for handling critical security events</li>
            <li>OTP controller with access controls and memory scrambling</li>
            <li>Flash controller with access controls and memory scrambling</li>
            <li>ROM and SRAM controllers with low-latency memory scrambling</li>
            <li>SoC Debug Controller</li>
            <li>Register-Access Control List (RACL) Controller</li>
            <li>Access Control Range Check</li>
          </ul>
        </li>
      </ul>
    </td>
    <td>
      <ul>
        <li>Memory:
          <ul>
            <li>1 MiB shared CTN SRAM (in wrapper)</li>
            <li>64 KiB main SRAM</li>
            <li>4 KiB retention SRAM</li>
            <li>4 KiB shared mailbox SRAM</li>
            <li>32 KiB ROM partition 1</li>
            <li>64 KiB ROM partition 2</li>
            <li>16 KiB (=128 Kibit) OTP</li>
          </ul>
        </li>
        <br></br>
        <li>I/O peripherals:
          <ul>
            <li>32 bit GPIO with 8 input period counters</li>
            <li>1x UART</li>
            <li>1x I2C with host and device modes</li>
            <li>1x SPI host with 1 chip select</li>
            <li>1x SPI device</li>
            <li>9x DOE Mailboxes</li>
            <li>1x JTAG Mailbox</li>
            <li>1x DMA Controller with support for inline hashing of transferred data with SHA-256, SHA-384, or SHA-512</li>
            <li>1x SoC Proxy module for external alerts and interrupt requests</li>
          </ul>
        </li>
        <br></br>
        <li>Other peripherals:
          <ul>
            <li>Clock, reset and power management</li>
            <li>Fixed-frequency timer</li>
            <li>Watchdog (always-on timer)</li>
          </ul>
        </li>
        <br></br>
        <li>Software:
          <ul>
            <li>Boot ROM code implementing secure boot, including owner-approved second signing, and chip configuration</li>
            <li>Bare metal top-level tests</li>
            <li>OpenTitan Crypto Library with OTBN accelerated standard algorithms for </li>
            <ul>
              <li>RSA 2K, 3K, 4K</li>
              <li>ECC with NIST P256/P384, Brainpool P256r1 or X25519/Ed25519</li>
              <li>SHA2-256, 384, 512</li>
            </ul>
            <li>SPHINCS+ PQ-secure boot using a stateless hash-based signatures scheme</li>
            <li>SPDM responder application</li>
          </ul>
        </li>
      </ul>
    </td>
  </tr>
</tbody>
</table>

## Discrete Earl Grey Differences

The Darjeeling configuration derived from the OpenTitan's discrete "Earl Grey" has been extended to meet the requirements for an SoC-integrated RoT.
The main processing elements and cryptographic features are significantly similar, while several unneeded IO peripherals in an integrated context have been removed. A set of new IP blocks have been developed to enable integration into a larger SoC:

- An [extended key manager block](../../ip/keymgr_dpe/README.md) with support for TCG’s DICE Protection Environment (DPE)
- A [DMA controller](../../ip/dma/README.md) facilitating data exchange between the OpenTitan IP and the SoC
- A [mailbox](../../ip/mbx/README.md) with TL-UL bus interface, configurable shared memory regions, and support for the PCIe Data Object Exchange (DOE) protocol
- A SoC proxy module that serves as a comportable fronted for external interrupts, alerts and the like
- An [SoC debug controller](../../ip/soc_dbg_ctrl/README.md), which controls debug and test access to the SoC
- An [access control range check module](../ip_autogen/ac_range_check/README.md) that ensures that Darjeeling can access only authorized addresses in the SoC
- A [register-access control list controller](../ip_autogen/racl_ctrl/README.md) that defines role-based access permissions to Darjeeling's registers
